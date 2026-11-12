(ns demo.authz
  "Authorization as checks: a refund request whose value proves that the permission service
  allowed it. Each printed line is a form, then what it returned or the error it threw, then
  the calls the permission service received.

      clojure -M:dev -m demo.authz"
  (:require
   [clojure.string :as str]
   [recognitum.core :as rec]
   [demo.permissions :as perms]
   [demo.show :refer [show *logs*]]))

(rec/defconcern access "Checks that ask the permission service.")

(defn non-blank? [s] (and (string? s) (not (str/blank? s))))

(rec/defproven Refund [actor order-id amount ^:optional note]
  rec/checks
  (actor    [] "the actor is named" (non-blank? actor))
  (order-id [] "the order id is a positive whole number" (pos-int? order-id))
  (amount   [] "the amount is a positive whole number of cents" (pos-int? amount))
  (note     [] "the note is text" (string? note))

  (may-refund [] ::access
    "the actor holds the refund grant for the order"
    (true? (rec/fetch perms/allowed [actor :refund order-id])))

  (within-limit [may-refund] ::access
    "the amount is within the actor's refund limit"
    (<= amount (or (rec/fetch perms/refund-limit actor) 0))))

(defn request->draft
  "A draft of a Refund from a request: the actor from the session, the rest from the form's
  string parameters. A parameter that does not parse is held as given, so its shape check
  fails on it."
  [{:keys [session params]}]
  (let [number (fn [s] (or (some-> s parse-long) s))]
    (cond-> (assoc (rec/draft Refund)
                   ::actor (:user session)
                   ::order-id (number (get params "order"))
                   ::amount (number (get params "amount")))
      (contains? params "note") (assoc ::note (get params "note")))))

(defn issue!
  "Issues the refund `r`. Throws unless `r` is a sealed Refund."
  [r]
  (when-not (and (instance? Refund r) (rec/sealed? r))
    (throw (ex-info "not a sealed Refund" {:value r})))
  (str "refunded " (::amount r) " cents on order " (::order-id r) " for " (::actor r)))

(defn under-limit
  "What each of `refunds`, maps of a Refund's fields, would answer if `user`'s refund limit
  were `cents`: true or a report. The service's limits are not changed, and no other reader of
  the service sees `cents`."
  [refunds user cents]
  (rec/probe-all Refund refunds rec/every
                 ;; For this call only, the checks that read `perms/refund-limit` get this
                 ;; function's answer: the service's own, with the one limit replaced.
                 {perms/refund-limit
                  (fn [users] (merge (perms/refund-limit users) (select-keys {user cents} users)))}))

(defn valid-on-the-day
  "What each of `refunds`, maps of a Refund's fields as the refunds table stores them, answers
  under the grants and limits of an earlier day: true or a report. `snapshot` holds that day's
  `:grants`, a set of `[user action order-id]`, and `:limits`, a map from user to cents."
  [refunds {:keys [grants limits]}]
  (rec/probe-all Refund refunds rec/every
                 ;; Both sources are answered from the snapshot, in the shape the service
                 ;; answers in, so the service is not called at all.
                 {perms/allowed      (fn [ks] (into {} (map (fn [k] [k (contains? grants k)])) ks))
                  perms/refund-limit (fn [users] (select-keys limits users))}))

(defn- request [user params] {:session {:user user} :params params})

(def ^:private dana-refunds-1500
  (request "dana" {"order" "42" "amount" "1500" "note" "damaged in transit"}))

(def ^:private held
  "Refunds that wait for a supervisor."
  [{::actor "eli" ::order-id 42 ::amount 2500}
   {::actor "eli" ::order-id 42 ::amount 900}
   {::actor "eli" ::order-id 41 ::amount 2500}])

(def ^:private refunds-table
  "Refunds issued last month, as their rows are stored."
  [{::actor "dana" ::order-id 42 ::amount 1500}
   {::actor "eli" ::order-id 41 ::amount 300}])

(def ^:private last-month
  "The grants and the limits as they stood when those refunds were issued."
  {:grants #{["dana" :refund 41] ["dana" :refund 42] ["eli" :refund 42]}
   :limits {"dana" 5000 "eli" 1000}})

(defn -main [& _]
  (perms/restore!)
  (binding [*logs* {"permission service" perms/calls}]
    (println "-- a request becomes a draft; the seal asks the permission service\n")
    (let [d (request->draft dana-refunds-1500)]
      (show d)
      (show (issue! d))
      (show (issue! (rec/seal d))))

    (println "-- a failed seal reports each failed check and the checks it blocked\n")
    (show (rec/seal (request->draft (request "eli" {"order" "42" "amount" "2500"}))))
    (show (rec/seal (request->draft (request "eli" {"order" "41" "amount" "15.00"}))))
    (show (rec/check (request->draft (request "eli" {"order" "41" "amount" "15.00"})) rec/every))

    (println "-- a draft remembers what passed: the shape checks first, the service at the seal\n")
    (let [d (request->draft (request "eli" {"order" "42" "amount" "800"}))]
      (show (rec/check d rec/shape))
      (show (rec/proven-checks d))
      (show (rec/seal d)))

    (println "-- requests checked in one pass share the service's calls\n")
    (show (rec/check-all [(request->draft dana-refunds-1500)
                          (request->draft (request "eli" {"order" "42" "amount" "900"}))
                          (request->draft (request "eli" {"order" "41" "amount" "900"}))]
                         access))

    (println "-- after a grant is revoked, a recheck asks the service again; a seal does not\n")
    (let [r (rec/seal (request->draft dana-refunds-1500))]
      (show (rec/check r access))
      (show (perms/revoke! "dana" :refund 42))
      (show (rec/recheck r access))
      (show (rec/seal (rec/draft r))))

    (println "-- an audit: dana's grant is gone today; was last month's refund valid when issued?\n")
    (show (mapv true? (rec/probe-all Refund refunds-table)))
    (show (mapv true? (valid-on-the-day refunds-table last-month)))
    (perms/restore!)

    (println "-- before a limit changes: which held refunds would pass under it, the service unchanged\n")
    (show (mapv true? (rec/probe-all Refund held)))
    (show (mapv true? (under-limit held "eli" 3000)))
    (show (mapv true? (under-limit held "eli" 500)))
    (show (mapv true? (rec/probe-all Refund held)))))
