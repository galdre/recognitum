(ns recognitum.check-test
  "Selections, check-all across types, and what proves? asks."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]
   [recognitum.engine :as engine]
   [recognitum.example.card :as card]
   [recognitum.example.db :as db]
   [recognitum.example.perms :as perms]
   [recognitum.heist :as h])
  (:import
   (recognitum.example.card Card Dashboard)
   (recognitum.heist Heist)))

(def row {::card/id 1 ::card/name "Plan" ::card/collection-id 1 ::card/archived false
          ::card/acting-user "ann"})

(def board {::card/id 7 ::card/title "Board" ::card/collection-id 2 ::card/acting-user "cy"})

;;; ------------------------------------------------------------------ selections

(deftest selections-name-checks-in-a-type
  (is (= #{::card/name ::card/collection-id ::card/archived} (rec/checks-of rec/shape Card)))
  (is (= #{::perms/may-write ::perms/current-may-write ::card/moves-only-where-allowed}
         (rec/checks-of perms/permission Card)
         (rec/checks-of ::perms/permission Card))
      "a concern by its var or its keyword")
  (is (= #{::card/owner-active} (rec/checks-of (rec/fetching db/users) Card)))
  (is (= #{::card/name ::card/collection-id ::card/archived ::card/not-archived-on-edit
           ::card/moves-only-where-allowed}
         (rec/checks-of rec/pure Card)))
  (is (= #{::perms/current-collection-exists ::perms/current-may-write ::card/not-archived-on-edit}
         (rec/checks-of (rec/union (rec/reading ::card/stored-collection-id)
                                   (rec/reading ::card/stored-archived))
                        Card)))
  (is (= #{::card/name} (rec/checks-of (rec/except rec/shape ::card/collection-id ::card/archived) Card)))
  (testing "a selection that names nothing in a type selects nothing there"
    (is (= #{} (rec/checks-of perms/permission Heist)))
    (is (rec/proves? h/italian-job perms/permission))))

(defn- refusal [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e [(ex-message e) (ex-data e)])))

(deftest a-keyword-naming-nothing-is-refused-when-the-selection-is-built
  (is (= ["no concern, bundle check or check of a type is named :recognitum.example.perms/permision"
          {:error :recognitum/unknown-name :name ::perms/permision}]
         (refusal #(rec/except rec/every ::perms/permision))))
  (is (= :recognitum/unknown-name (:error (second (refusal #(rec/union rec/shape ::card/nmae))))))
  (is (= :recognitum/unknown-name (:error (second (refusal #(rec/union :no.such.ns/check))))))
  (testing "a concern, a bundle check, or a check of a type of the keyword's namespace is accepted"
    (is (map? (rec/union ::perms/permission ::perms/may-write ::card/name ::card/owner-active)))))

(deftest an-own-check-id-a-type-lacks-is-refused-when-the-selection-meets-the-type
  (is (= ["recognitum.example.card/Card has no check :recognitum.example.card/nmae, and no concern or bundle check is named :recognitum.example.card/nmae"
          {:error :recognitum/unknown-name :name ::card/nmae :type 'recognitum.example.card/Card}]
         (refusal #(rec/checks-of ::card/nmae Card))))
  (is (= 'recognitum.heist/Heist (:type (second (refusal #(rec/checks-of ::card/name Heist)))))
      "another type's own check")
  (is (= 'recognitum.example.card/Dashboard
         (:type (second (refusal #(rec/checks-of (rec/union ::card/owner-active) Dashboard))))))
  (is (= :recognitum/unknown-name (:error (second (refusal #(rec/check (rec/draft Card) ::perms/permision)))))))

(deftest a-concern-or-bundle-check-a-type-lacks-selects-nothing-in-it
  (is (= #{} (rec/checks-of ::perms/permission Heist)))
  (is (= #{} (rec/checks-of ::perms/may-write Heist)))
  (is (= #{} (rec/checks-of perms/may-write Heist))))

;;; ------------------------------------------------------------------ check-all

(deftest check-all-runs-a-group-of-several-types-in-one-run
  (let [runs (atom [])
        run-all engine/run-all
        drafts [(into (rec/draft Card) row)
                (into (rec/draft Dashboard) board)
                (into (rec/draft Card) (assoc row ::card/acting-user "bob"))]]
    (with-redefs [engine/run-all (fn [items] (swap! runs conj (count items)) (run-all items))]
      (let [[a b c] (rec/check-all drafts perms/may-write)]
        (is (true? a))
        (is (true? b))
        (is (= #{::perms/may-write} (set (keys (:failed c)))))))
    (is (= [3] @runs))))

(def ^:private runs (atom []))

(rec/defproven Counted [a b]
  rec/checks
  (a [] (swap! runs conj ::a) (int? a))
  (b [] (swap! runs conj ::b) (int? b))
  (a-below-b [] (swap! runs conj ::a-below-b) (< a b)))

(deftest check-all-remembers-on-each-draft-as-check-does
  (let [d1 (into (rec/draft Counted) {::a 1 ::b 2})
        d2 (into (rec/draft Counted) {::a 3 ::b 4})
        v (map->Counted {::a 5 ::b 6})]
    (reset! runs [])
    (is (= [true true true] (rec/check-all [d1 d2 v] rec/shape)))
    (is (= {::a 2 ::b 2} (frequencies @runs)) "the sealed value runs nothing")
    (is (= #{::a ::b} (rec/proven-checks d1) (rec/proven-checks d2)))
    (is (rec/sealed? v))
    (is (= (rec/checks-of rec/every Counted) (rec/proven-checks v)))
    (testing "sealing each draft runs only the rest"
      (reset! runs [])
      (is (instance? Counted (rec/seal d1)))
      (is (instance? Counted (rec/seal d2)))
      (is (= [::a-below-b ::a-below-b] @runs))))
  (testing "a failed check is not remembered, and a check that did not run is left as it was"
    (let [d (into (rec/draft Counted) {::a 1 ::b "two"})]
      (rec/check d ::a)
      (is (= [{:failed {::b {:data false :blocked #{::a-below-b}}} :blocked #{::a-below-b}}]
             (rec/check-all [d] rec/every)))
      (is (= #{::a} (rec/proven-checks d))))))

(deftest check-all-runs-the-checks-of-a-displaced-value
  ;; A value of an earlier definition passes nothing, so check-all runs its definition's checks.
  (let [ns' (create-ns 'recognitum.check-test.displaced)
        ran (atom 0)
        _ (intern ns' 'ran ran)
        define #(binding [*ns* ns']
                  (refer-clojure)
                  (eval '(recognitum.core/defproven R [a] recognitum.core/checks (a [] (swap! ran inc) (int? a)))))
        _ (define)
        old ((ns-resolve ns' 'map->R) {:recognitum.check-test.displaced/a 1})]
    (define)
    (reset! ran 0)
    (let [rs (rec/check-all [old] rec/every)]
      (is (vector? rs))
      (is (= [true] rs)))
    (is (= 1 @ran))))

(deftest check-all-runs-nothing-on-sealed-values
  (let [runs (atom 0)
        run-all engine/run-all
        values [(card/map->Card row) h/italian-job]]
    (with-redefs [engine/run-all (fn [items] (swap! runs inc) (run-all items))]
      (is (= [true true] (rec/check-all values rec/every))))
    (is (zero? @runs))))

(deftest a-wait-pulls-back-a-check-that-except-removed
  (let [d (into (rec/draft Card) (dissoc row ::card/acting-user))
        sel (rec/except rec/every perms/permission)]
    (testing "owner-active waits on collection-exists only, so leaving out permissions leaves out may-write"
      (is (true? (rec/check d sel))))
    (testing "a check that waits on may-write pulls it back, and the report says why it ran"
      (let [T (binding [*ns* (the-ns 'recognitum.example.card)]
                (eval '(rec/defproven Puller [collection-id ^:optional acting-user]
                         perms/collection-write
                         (user [] acting-user)
                         (collection-id [] collection-id)
                         rec/checks
                         (audited [perms/collection-write] true))))
            r (rec/check (into (rec/draft T) {::card/collection-id 1}) sel)]
        (is (= #{::perms/may-write} (set (keys (:failed r)))))
        (is (= #{::card/audited} (get-in r [:pulled-back ::perms/may-write :waited-on-by])))
        (is (re-find #"ran although an except removed it" (get-in r [:pulled-back ::perms/may-write :hint])))
        (testing "and check-all reports it alike, for each draft of a group"
          (let [d (into (rec/draft T) {::card/collection-id 1})]
            (is (= [r r] (rec/check-all [d (into (rec/draft T) {::card/collection-id 1})] sel)))))))))

;;; ------------------------------------------------------------------ proves?

(deftest proves?-holds-for-every-sealed-value-and-asks-a-drafts-memory
  (is (rec/proves? (card/map->Card row) rec/every))
  (let [d (into (rec/draft Card) row)]
    (is (not (rec/proves? d rec/shape)))
    (rec/check d rec/shape)
    (is (rec/proves? d rec/shape))
    (testing "a check runs with what it waits on"
      (rec/check d ::card/moves-only-where-allowed)
      (is (every? (rec/proven-checks d) [::perms/may-write ::perms/collection-exists])))
    (testing "every shape check of a present or required field is a floor under each proof"
      (let [d (into (rec/draft Card) row)]
        (rec/check d ::perms/collection-exists)
        (is (not (rec/proves? d ::perms/collection-exists)))
        (rec/check d rec/shape)
        (is (rec/proves? d ::perms/collection-exists))))
    (is (contains? (rec/proven-concerns (rec/draft (card/map->Card row))) ::perms/permission)))
  (is (not (rec/proves? row rec/every)) "a plain map proves nothing"))

(deftest the-floor-under-a-drafts-proof-is-its-shape-checks-only
  (let [d (into (rec/draft Counted) {::a 1 ::b 2})]
    (rec/check d ::a)
    (is (not (rec/proves? d ::a)) "the shape check of the required field b is part of every proof")
    (rec/check d ::b)
    (is (rec/proves? d ::a))
    (is (not (contains? (rec/proven-checks d) ::a-below-b)) "an invariant that was not asked for is not")))

;;; ------------------------------------------------------------- runs on the calling thread

(def ^:private lookups (atom 0))

(defn- listed
  "A source that lists every key it is asked for. Counts its calls."
  [ks]
  (swap! lookups inc)
  (into {} (map (fn [k] [k true])) ks))

(rec/defproven Sourced [a b crew]
  rec/checks
  (a [] (int? a))
  (b [] (int? b))
  (crew [] (set? crew))
  (all-listed [] (every? true? (vals (rec/fetch-each listed crew)))))

(rec/defproven Unsourced [a b]
  rec/checks
  (a [] (int? a))
  (b [] (int? b))
  (a-below-b [] (< a b)))

(defn- engine-runs
  "How many times `f` calls the engine's full run, and what it returns."
  [f]
  (let [n (atom 0)
        run-all engine/run-all]
    (with-redefs [engine/run-all (fn [items] (swap! n inc) (run-all items))]
      (let [r (f)] [@n r]))))

(deftest a-run-with-every-source-check-assumed-skips-the-engines-full-run
  ;; Every source check left out of a run, the checks left run on the calling thread, which
  ;; costs a fraction of the full run.
  (let [v (map->Sourced {::a 1 ::b 2 ::crew #{:x}})]
    (testing "a type with no source check"
      (is (= [0 true] (update (engine-runs #(map->Unsourced {::a 1 ::b 2})) 1 rec/sealed?)))
      (is (= [0 true] (update (engine-runs #(merge (map->Unsourced {::a 1 ::b 2}) {::a 0 ::b 3})) 1 rec/sealed?)))
      (is (= [0 true] (update (engine-runs #(rec/seal (into (rec/draft Unsourced) {::a 1 ::b 2}))) 1 rec/sealed?))))
    (testing "a type with one, where the run leaves it out"
      (is (= [0 true] (update (engine-runs #(merge v {::a 5 ::b 6})) 1 rec/sealed?)))
      (is (= [0 true] (update (engine-runs #(rec/seal (assoc (rec/draft v) ::a 7))) 1 rec/sealed?)))
      (is (= [0 true] (engine-runs #(rec/check (assoc (rec/draft v) ::b 3) ::b)))))
    (testing "a run that includes it goes through the full run, which calls the source"
      (reset! lookups 0)
      (is (= [1 true] (update (engine-runs #(merge v {::a 5 ::crew #{:y}})) 1 rec/sealed?)))
      (is (= 1 @lookups)))))

(rec/defproven Twelve [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11]
  rec/checks
  (f0 [] (int? f0))
  (f1 [] (int? f1))
  (f2 [] (int? f2))
  (f3 [] (int? f3))
  (f4 [] (int? f4))
  (f5 [] (int? f5))
  (f6 [] (int? f6))
  (f7 [] (int? f7))
  (f8 [] (int? f8))
  (f9 [] (int? f9))
  (f10 [] (int? f10))
  (f11 [] (int? f11)))

(deftest a-seal-builds-no-runner-for-a-draft-that-passes-everything-or-past-a-thousand-masks
  ;; each check reads its own field alone, so each set of fields a draft changes is its own mask
  (let [ks (mapv #(keyword "recognitum.check-test" (str "f" %)) (range 12))
        v (map->Twelve (zipmap ks (range)))
        writing (fn [bits x] (reduce (fn [d i] (if (bit-test bits i) (assoc d (ks i) x) d)) (rec/draft v) (range 12)))
        error (fn [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (:error (ex-data e)))))
        builds (atom 0)
        runner engine/runner]
    (with-redefs [engine/runner (fn [& args] (swap! builds inc) (apply runner args))]
      (is (= v (rec/seal (rec/draft v))))
      (is (= 0 @builds) "a draft that passes every check runs none")
      (doseq [bits (range 1 1100)]
        (rec/seal (writing bits 100)))
      (is (= 1000 @builds) "one runner for each of the first thousand masks, none after")
      (is (= :recognitum/check-failed (error #(rec/seal (writing 2r101 "x"))))
          "a mask kept still runs its checks")
      (is (= :recognitum/check-failed (error #(rec/seal (writing 2r110000000000 "x"))))
          "a mask past the thousand still runs its checks")
      (is (= 100 (::f11 (rec/seal (writing 2r110000000000 100)))))
      (is (= 1000 @builds)))))
