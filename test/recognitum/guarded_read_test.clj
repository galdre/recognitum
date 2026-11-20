;; The README states this behavior: a read in a branch not taken is never sent.
(ns recognitum.guarded-read-test
  "A read of a source that sits in a branch a body does not take is never sent to the source:
  for each form that can guard a read, which keys reach the source, in how many calls, and what
  the check answers."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]))

(def ^:private calls
  "The keys of each source call, in order, since the last reset."
  (atom []))

(defn known
  "A source: every key it is asked for is known, so answers true; it records each call."
  [ks]
  (swap! calls conj (vec ks))
  (zipmap ks (repeat true)))

(defn owner
  "A source: the owner of each id, 1 being owned by :ann and every other id by no one."
  [ks]
  (swap! calls conj [:owner (vec ks)])
  (into {} (map (fn [k] [k (when (= 1 k) :ann)])) ks))

(defn- run
  "`[answer calls]`: what `(f)` returns, or the ex-data of what it throws, and the source calls
  it made."
  [f]
  (reset! calls [])
  (let [r (try (f) (catch clojure.lang.ExceptionInfo e (ex-data e)))]
    [r @calls]))

(defn- failed-ids [r] (set (keys (:failed r))))

;;; ------------------------------------------------------------------ the types

(rec/defproven ByOr [x]
  rec/checks
  (by-or [] (or (nil? x) (true? (rec/fetch known x)))))

(rec/defproven ByIf [x]
  rec/checks
  (by-if [] (if (nil? x) true (true? (rec/fetch known x)))))

(rec/defproven ByWhen [x]
  rec/checks
  (by-when [] (let [r (when (some? x) (rec/fetch known x))] (or (nil? x) (true? r)))))

(rec/defproven ByAnd [x]
  rec/checks
  (by-and [] (let [r (and (some? x) (rec/fetch known x))] (or (nil? x) (true? r)))))

(rec/defproven ByCond [x]
  rec/checks
  (by-cond [] (cond (nil? x) true
                    (= :skip x) true
                    :else (true? (rec/fetch known x)))))

(rec/defproven ByCase [x]
  rec/checks
  (by-case [] (case x
                nil true
                :skip true
                (true? (rec/fetch known x)))))

(rec/defproven BySomeThread [x]
  rec/checks
  (by-some-thread [] (not= false (some->> x (rec/fetch known)))))

(rec/defproven BySomeArrow [x]
  rec/checks
  (by-some-arrow [] (not= false (some-> x (as-> k (rec/fetch known k))))))

(rec/defproven ByExtant [^:optional x]
  rec/checks
  (by-extant [] (rec/when-extant x (true? (rec/fetch known x)))))

(rec/defproven Chained [id]
  rec/checks
  (chained [] (let [who (rec/fetch owner id)]
                (or (nil? who) (true? (rec/fetch known who))))))

(rec/defproven Many [xs]
  rec/checks
  (many [] (if (empty? xs) true (every? true? (vals (rec/fetch-each known xs))))))

(rec/defproven EmptyEach [xs]
  rec/checks
  (empty-each [] (= {} (rec/fetch-each known xs))))

(rec/defproven Waits [x]
  rec/checks
  (positive [] (pos? x))
  (known-x [positive] (true? (rec/fetch known x))))

(rec/defproven InTry [x]
  rec/checks
  (try-body [] (try (or (nil? x) (true? (rec/fetch known [:body x])))
                    (catch Exception _ false)))
  (try-catch [] (try (if (nil? x) (throw (ex-info "nil" {})) true)
                     (catch clojure.lang.ExceptionInfo _ (true? (rec/fetch known [:catch x])))))
  (try-untaken-catch [] (try true
                             (catch Exception _ (true? (rec/fetch known [:never x])))))
  (try-finally [] (try true
                       (finally (when (some? x) (rec/fetch known [:finally x]))))))

(rec/defproven InLoop [ks]
  rec/checks
  (in-loop [] (loop [[k & more] ks]
                (cond (nil? k) true
                      (= :stop k) true
                      :else (if (true? (rec/fetch known k)) (recur more) false)))))

(rec/defproven Unguarded [x]
  rec/checks
  (unguarded [] (or (true? (rec/fetch known x)) (nil? x))))

(defn- one-check
  "`[answer calls]` of building a value of `T` from `m` with `map->T`, the answer true where it
  built."
  [build m]
  (run #(do (build m) true)))

;;; ------------------------------------------------------------------ one value

(deftest each-guard-keeps-its-read-from-the-source
  (doseq [[label build k] [["or" map->ByOr ::x]
                           ["if" map->ByIf ::x]
                           ["when" map->ByWhen ::x]
                           ["and" map->ByAnd ::x]
                           ["cond" map->ByCond ::x]
                           ["case" map->ByCase ::x]
                           ["some->>" map->BySomeThread ::x]
                           ["some->" map->BySomeArrow ::x]]]
    (testing label
      (testing "with the guarded key nil: the source is not called, and the check passes"
        (is (= [true []] (one-check build {k nil}))))
      (testing "with the key set: one call with that key"
        (is (= [true [[7]]] (one-check build {k 7})))))))

(deftest a-read-before-its-guard-sends-the-nil-key
  (is (= [true [[nil]]] (one-check map->Unguarded {::x nil}))
      "the source records a nil key where a body asks for one"))

(deftest cond-and-case-skip-every-key-their-guard-names
  (is (= [true []] (one-check map->ByCond {::x :skip})))
  (is (= [true []] (one-check map->ByCase {::x :skip}))))

(deftest when-extant-keeps-the-read-of-an-absent-field-from-the-source
  (is (= [true []] (one-check map->ByExtant {})))
  (is (= [true [[7]]] (one-check map->ByExtant {::x 7}))))

(deftest a-guard-on-a-fetched-answer-keeps-the-second-read-from-the-source
  (testing "the first read answers nil: only it is sent"
    (is (= [true [[:owner [2]]]] (one-check map->Chained {::id 2}))))
  (testing "the first read answers :ann: the second read is sent with that answer"
    (is (= [true [[:owner [1]] [:ann]]] (one-check map->Chained {::id 1})))))

(deftest fetch-each-in-a-branch-not-taken-is-not-sent
  (is (= [true []] (one-check map->Many {::xs []})))
  (is (= [true [[1 2]]] (one-check map->Many {::xs [1 2]}))))

(deftest fetch-each-of-no-keys-calls-no-source
  (is (= [true []] (one-check map->EmptyEach {::xs []}))))

(deftest a-check-blocked-by-a-failed-wait-sends-no-read
  (let [[r cs] (one-check map->Waits {::x -1})]
    (is (= #{::positive} (failed-ids r)) "the wait fails")
    (is (contains? (:blocked r) ::known-x) "the reading check is blocked")
    (is (= [] cs)))
  (is (= [true [[3]]] (one-check map->Waits {::x 3}))))

;;; ------------------------------------------------------------------ try and loop

(deftest reads-in-try-catch-and-finally-are-sent-only-where-reached
  (testing "x nil: only the catch is reached, and its read is sent"
    (is (= [true [[[:catch nil]]]] (one-check map->InTry {::x nil}))))
  (testing "x set: the body's read and the finally's read are sent; no catch runs"
    (let [[r cs] (one-check map->InTry {::x 4})]
      (is (true? r))
      (is (= #{[:body 4] [:finally 4]} (set (apply concat cs))))
      (is (= 1 (count cs)) "both reads are in the first wave, so one call")
      (is (not-any? #(= :never (first %)) (apply concat cs))))))

(deftest a-loop-that-stops-early-sends-only-the-keys-it-reached
  (is (= [true [[1]]] (one-check map->InLoop {::ks [1 :stop 3]})))
  (is (= [true [[1] [2] [3]]] (one-check map->InLoop {::ks [1 2 3]}))
      "each pass reads once, so each key is a call of its own")
  (is (= [true []] (one-check map->InLoop {::ks [:stop 1]}))))

;;; ------------------------------------------------------------------ many values, probe, selections

(deftest seal-all-sends-only-the-keys-of-the-drafts-that-take-the-branch
  (let [ds (mapv #(into (rec/draft ByOr) {::x %}) [nil 1 nil 2 1])
        [r cs] (run #(rec/seal-all ds))]
    (is (= 5 (count r)))
    (is (= [[1 2]] cs) "one call, each reached key once, no nil")))

(deftest check-all-over-several-guards-shares-one-call
  (let [ds [(into (rec/draft ByOr) {::x nil}) (into (rec/draft ByIf) {::x 5})
            (into (rec/draft ByCase) {::x :skip}) (into (rec/draft BySomeThread) {::x 5})
            (into (rec/draft Chained) {::id 2})]
        [r cs] (run #(rec/check-all ds rec/every))]
    (is (= [true true true true true] r))
    (is (= [[5] [:owner [2]]] cs))))

(deftest probe-sends-no-guarded-read
  (is (= [true []] (run #(rec/probe ByOr {::x nil}))))
  (is (= [true [[9]]] (run #(rec/probe ByOr {::x 9}))))
  (is (= [[true true true] [[4]]] (run #(rec/probe-all ByOr [{::x nil} {::x 4} {::x nil}])))))

(deftest probe-overrides-receive-no-guarded-read
  (let [seen (atom [])
        stub (fn [ks] (swap! seen conj (vec ks)) (zipmap ks (repeat true)))]
    (is (= [[true true] []] (run #(rec/probe-all ByOr [{::x nil} {::x 3}] rec/every {known stub}))))
    (is (= [[3]] @seen))))

(deftest a-selection-without-the-reading-check-sends-nothing
  (doseq [sel [rec/pure rec/shape (rec/except rec/every (rec/fetching known))]]
    (is (= [true []] (run #(rec/check (into (rec/draft ByOr) {::x 3}) sel))))))

(deftest a-selection-of-the-reading-check-sends-only-reached-keys
  (is (= [true []] (run #(rec/check (into (rec/draft ByOr) {::x nil}) (rec/fetching known)))))
  (is (= [true [[3]]] (run #(rec/check (into (rec/draft ByOr) {::x 3}) (rec/fetching known))))))

;;; ------------------------------------------------------------------ reads the macros refuse

(defn- refusal
  "The message of what defining `form` in this namespace throws, or nil."
  [form]
  (try (binding [*ns* (the-ns 'recognitum.guarded-read-test)] (eval form)) nil
       (catch Throwable t
         (loop [t t] (if (.getCause t) (recur (.getCause t)) (.getMessage t))))))

(deftest a-read-inside-a-fn-the-body-builds-is-refused
  (testing "a fn literal called only when the guard allows"
    (is (re-find #"inside a fn the check body builds"
                 (str (refusal '(rec/defproven ByFnLit [x]
                                  rec/checks
                                  (by-fn-lit [] (let [f #(rec/fetch known x)]
                                                  (or (nil? x) (true? (f)))))))))))
  (testing "a letfn called only when the guard allows"
    (is (re-find #"inside a fn the check body builds"
                 (str (refusal '(rec/defproven ByLetfn [x]
                                  rec/checks
                                  (by-letfn [] (letfn [(g [] (rec/fetch known x))]
                                                 (or (nil? x) (true? (g))))))))))))
