(ns recognitum.bundle-test
  "Bundles bound into types: input clauses, `:when-extant`, copies, overrides, waits on bundle
  checks, and concerns."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]
   [recognitum.example.ballot :as ballot]
   [recognitum.example.db :as db]
   [recognitum.example.perms :as perms])
  (:import
   (recognitum.example.ballot Ballot Tally)))

(defn- failed [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:failed (ex-data e)))))

(def row {::ballot/id 1 ::ballot/choice "Yes" ::ballot/ballot-box-id 1 ::ballot/spoiled false
          ::ballot/cast-by "ann"})

(deftest a-bundle-is-a-var-and-each-check-a-var-with-its-id
  (is (= [:recognitum.example.perms/box-exists :recognitum.example.perms/may-cast]
         (mapv :id [perms/box-exists perms/may-cast])))
  (is (= "the voter may cast into the ballot box" (:doc (meta #'perms/may-cast))))
  (is (= #{::perms/permission} (:concerns perms/may-cast))))

(deftest a-bound-bundle-reads-its-inputs-from-the-fields
  (is (instance? Ballot (ballot/map->Ballot row)))
  (is (= {:data false :doc "the voter may cast into the ballot box"
          :blocked #{::ballot/moves-only-where-allowed}}
         (::perms/may-cast (failed #(ballot/map->Ballot (assoc row ::ballot/cast-by "bob")))))))

(deftest an-input-whose-field-is-absent-is-absent
  (is (= {:absent :voter} (:data (::perms/may-cast (failed #(ballot/map->Ballot (dissoc row ::ballot/cast-by))))))))

(deftest when-extant-skips-a-binding-as-passing
  (testing "no stored ballot box: the copy's checks pass without running"
    (is (contains? (rec/proven-checks (ballot/map->Ballot row)) ::perms/stored-may-cast)))
  (testing "a stored ballot box runs them"
    (is (= #{::perms/stored-may-cast}
           (set (keys (failed #(ballot/map->Ballot (assoc row ::ballot/stored-ballot-box-id 2))))))))
  (testing "writing the field later runs the binding it gated"
    (let [c (ballot/map->Ballot row)]
      (is (instance? Ballot (assoc c ::ballot/stored-ballot-box-id 3)))
      (is (contains? (failed #(assoc c ::ballot/stored-ballot-box-id 2)) ::perms/stored-may-cast)))))

(deftest a-copy-has-its-own-ids-in-its-namespace-and-keeps-concerns
  (is (= ::perms/stored-may-cast (:id perms/stored-may-cast)))
  (is (= #{::perms/permission} (:concerns perms/stored-may-cast)))
  (is (= #{::perms/stored-box-exists} (:waits perms/stored-may-cast))))

(deftest an-override-keeps-the-id-and-concerns
  (let [d (ballot/map->Tally {::ballot/id 1 ::ballot/label "Turnout" ::ballot/ballot-box-id 2 ::ballot/counted-by "cy"})]
    (is (instance? Tally d))
    (is (= #{::perms/may-cast} (rec/checks-of perms/permission d)))
    (is (= "tallies also allow the ballot box's tellers"
           (:doc (::perms/may-cast (failed #(assoc d ::ballot/counted-by "dee"))))))))

(deftest an-override-inherits-its-bindings-when-extant
  (let [T (binding [*ns* (the-ns 'recognitum.example.ballot)]
            (eval '(rec/defproven Gated [id ^:optional cast-by ^:optional stored-ballot-box-id]
                     ^{:when-extant stored-ballot-box-id}
                     perms/cast-into-stored-box
                     (voter [] cast-by)
                     (ballot-box-id [] stored-ballot-box-id)
                     rec/checks
                     (perms/stored-may-cast [] :override false))))
        make @(ns-resolve 'recognitum.example.ballot 'map->Gated)]
    (is (instance? T (make {::ballot/id 1})) "skipped where the gate field is absent")
    (is (contains? (failed #(make {::ballot/id 1 ::ballot/stored-ballot-box-id 1})) ::perms/stored-may-cast))))

(deftest waits-name-bundle-checks
  (testing "a check that waits on a failed bundle check is blocked by it"
    (is (= #{::ballot/moves-only-where-allowed}
           (:blocked (::perms/may-cast (failed #(ballot/map->Ballot (assoc row ::ballot/cast-by "bob"))))))))
  (testing "selections name bundle checks and bundles by their vars"
    (is (= #{::perms/may-cast ::perms/stored-may-cast}
           (rec/checks-of (rec/union perms/may-cast perms/stored-may-cast) Ballot)))
    (is (= #{::perms/box-exists ::perms/may-cast} (rec/checks-of perms/cast-into-box Ballot)))))

(deftest a-bundle-check-waits-on-the-shape-checks-of-the-fields-its-inputs-read
  (reset! db/calls [])
  (let [e (try (ballot/map->Ballot (assoc row ::ballot/ballot-box-id "one"))
               (catch clojure.lang.ExceptionInfo e (ex-data e)))]
    (is (= #{::ballot/ballot-box-id} (set (keys (:failed e)))))
    (is (every? (:blocked e) [::perms/box-exists ::perms/may-cast ::ballot/officer-active
                              ::ballot/moves-only-where-allowed]))
    (is (empty? @db/calls) "nothing read the ballot box")))

(deftest a-check-reads-a-source-keyed-by-another-read
  (is (= {:data false :doc "the ballot box's officer is active" :blocked #{}}
         (::ballot/officer-active (failed #(ballot/map->Ballot (assoc row ::ballot/ballot-box-id 3 ::ballot/cast-by "ann"))))))
  (reset! db/calls [])
  (ballot/map->Ballot row)
  (is (some #(= :officers (first %)) @db/calls)))

(def ^:private clause-runs (atom []))

(rec/defchecks positives [x y]
  rec/checks
  (x-positive [] (pos? x))
  (y-positive [] (pos? y)))

(rec/defproven Both [a b]
  positives
  (x [] (swap! clause-runs conj :x) (if (= -13 a) (throw (IllegalStateException. "unlucky")) a))
  (y [] (swap! clause-runs conj :y) b)
  rec/checks
  (a [] (int? a))
  (b [] (int? b)))

(deftest an-input-clause-runs-only-for-the-checks-that-read-its-input
  (testing "each clause runs once per value, for its one reader"
    (reset! clause-runs [])
    (is (instance? Both (map->Both {::a 1 ::b 2})))
    (is (= {:x 1 :y 1} (frequencies @clause-runs))))
  (testing "a reader that a shape check blocks runs no clause"
    (reset! clause-runs [])
    (is (= #{::a} (set (keys (failed #(map->Both {::a "one" ::b 2}))))))
    (is (= [:y] @clause-runs)))
  (testing "a throw from a clause propagates only when its reader runs"
    (let [d (into (rec/draft Both) {::a -13 ::b 2})]
      (reset! clause-runs [])
      (is (true? (rec/check d y-positive)))
      (is (= [:y] @clause-runs))
      (is (thrown-with-msg? IllegalStateException #"unlucky" (rec/check d x-positive))))))

(defn- refusal [form]
  (try (binding [*ns* (the-ns 'recognitum.bundle-test)] (eval form)) nil
       (catch clojure.lang.Compiler$CompilerException e (:message (ex-data (ex-cause e))))))

(deftest a-bare-wait-on-a-bundle-of-this-namespace-says-to-qualify-it
  (is (= (str "wait positives of c is not a check of Bare. Its own checks: c."
              " A wait on a bundle is qualified: recognitum.bundle-test/positives")
         (refusal '(rec/defproven Bare [a b]
                     positives (x [] a) (y [] b)
                     rec/checks (c [positives] true)))))
  (is (= (str "wait x-positive of c is not a check of Bare. Its own checks: c."
              " A wait on a bundle's check is qualified: recognitum.bundle-test/x-positive")
         (refusal '(rec/defproven Bare [a b]
                     positives (x [] a) (y [] b)
                     rec/checks (c [x-positive] true)))))
  (is (nil? (refusal '(rec/defproven Qualified [a b]
                        positives (x [] a) (y [] b)
                        rec/checks (c [recognitum.bundle-test/positives] true))))
      "qualified, the wait is accepted"))

(rec/defcopy other-cast-into-box perms/cast-into-box
  {box-exists other-box-exists
   may-cast   other-may-cast})

(deftest a-copys-ids-are-in-the-namespace-of-the-copy
  (is (= [::other-box-exists ::other-may-cast]
         (mapv :id [other-box-exists other-may-cast])))
  (is (= #{::other-box-exists} (:waits other-may-cast)))
  (is (= #{::perms/permission} (:concerns other-may-cast))))

(deftest a-qualified-clause-replaces-a-bundle-check-only-when-marked
  (is (= (str "recognitum.bundle-test/x-positive is qualified:"
              " write :override after its waits to replace that bundle check")
         (refusal '(rec/defproven Unmarked [a b]
                     positives (x [] a) (y [] b)
                     rec/checks (recognitum.bundle-test/x-positive [] true)))))
  (is (= ":override needs a qualified bundle check, got x-positive"
         (refusal '(rec/defproven Plain [a b]
                     positives (x [] a) (y [] b)
                     rec/checks (x-positive [] :override true)))))
  (is (nil? (refusal '(rec/defproven Marked [a b]
                        positives (x [] a) (y [] b)
                        rec/checks (recognitum.bundle-test/x-positive [] :override true))))
      "marked, the override is accepted"))

(deftest two-input-clauses-of-one-name-are-refused
  (is (= "two input clauses of positives are named x"
         (refusal '(rec/defproven Twice [a b]
                     positives (x [] a) (x [] 1) (y [] b)
                     rec/checks (a [] true))))))

(deftest a-bundle-takes-a-plain-name-and-a-vector-of-plain-inputs
  (let [said (str "defchecks takes a name, a docstring if any, a vector of plain input symbols,"
                  " rec/checks and clauses")]
    (is (= said (refusal '(rec/defchecks some.ns/qualified [a] rec/checks (x [] a)))))
    (is (= said (refusal '(rec/defchecks inputs-unplain [a 1] rec/checks (x [] a)))))
    (is (= said (refusal '(rec/defchecks inputs-unvectored (a) rec/checks (x [] a)))))))

(deftest a-bundle-checks-wait-names-a-check-of-its-bundle
  (is (= "wait y of x is not a check of waits-wide. Its checks: x"
         (refusal '(rec/defchecks waits-wide [a] rec/checks (x [y] a))))))

(deftest a-copy-takes-a-map-of-plain-names
  (let [said (str "defcopy takes a map from each check of perms/cast-into-box to its new name:"
                  " {check new-name ...}")]
    (is (= said (refusal '(rec/defcopy named-by-string perms/cast-into-box
                            {box-exists "c-exists" may-cast c-may-cast}))))
    (is (= said (refusal '(rec/defcopy named-qualified perms/cast-into-box
                            {box-exists a/c-exists may-cast c-may-cast}))))))

(deftest a-copy-redefines-no-check-of-another-bundle-here
  (is (= "new name other-may-cast would redefine recognitum.bundle-test/other-may-cast"
         (refusal '(rec/defcopy third-cast-into-box perms/cast-into-box
                     {box-exists third-box-exists may-cast other-may-cast}))))
  (is (= `other-cast-into-box (:bundle other-may-cast)) "the other bundle's check is unchanged"))
