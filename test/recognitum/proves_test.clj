(ns recognitum.proves-test
  "`rec/proves?` reads its selection before it answers, for a sealed value and a draft of a
  current definition alike, and is false while a draft holds a key its type does not declare;
  `rec/seal` of a sealed value reads its selection as `proves?` does."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]))

(rec/defconcern authorized "Whether the payment may go out.")
(rec/defconcern audit "Checks an auditor reads.")

(rec/defchecks spare "A bundle no type here binds." [x]
  rec/checks
  (spare-int [] (int? x)))

(def ^:private log (atom []))

(defn- ran! [id] (swap! log conj id) true)

(rec/defproven Payment [amount ^:optional note]
  rec/checks
  (amount [] (ran! ::amount) (pos-int? amount))
  (under-limit [] authorized (ran! ::under-limit) (< amount 100)))

(rec/defproven Holder [held n]
  rec/checks
  (n [] (ran! ::n) (int? n)))

(rec/defproven-in Ballot [choice]
  rec/checks
  (choice [] (ran! ::choice) (string? choice)))

(defn- outcome
  "`[answer runs]`: what `(f)` returns, or the `:error` of the ex-info it throws, and the checks
  that ran meanwhile."
  [f]
  (reset! log [])
  (let [r (try (f) (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))]
    [r @log]))

(def ^:private unknown
  "What is no selection of `Payment`, each with the `:error` of its refusal: keywords that name
  nothing, a check id of another type, and things that are no selection."
  [[::typo :recognitum/unknown-name] [:no.such/thing :recognitum/unknown-name] [::n :recognitum/unknown-name]
   [42 :recognitum/not-a-selection] [nil :recognitum/not-a-selection] ["s" :recognitum/not-a-selection]])

(defn- payments
  "A sealed value and drafts of `Payment`: whole, checked or not; lacking `amount`; holding nothing."
  []
  (let [whole (into (rec/draft Payment) {::amount 50})]
    [["a sealed value" (map->Payment {::amount 50})]
     ["a draft holding every required field" whole]
     ["a checked draft holding every required field" (doto (into (rec/draft Payment) {::amount 50}) (rec/check rec/every))]
     ["a draft lacking amount" (into (rec/draft Payment) {::note "n"})]
     ["a draft holding nothing" (rec/draft Payment)]
     ["a checked draft holding an undeclared key" (doto (into (rec/draft Payment) {::amount 50 :admin? true})
                                                    (rec/check rec/every))]]))

(deftest proves?-reads-the-selection-first
  (doseq [[label x] (payments), [sel want] unknown]
    (let [before (rec/proven-checks x)]
      (is (= [want []] (outcome #(rec/proves? x sel))) (str label ", " (pr-str sel)))
      (is (= before (rec/proven-checks x)) label))))

(deftest proves?-reads-the-selection-of-a-defproven-in-value-first
  (doseq [x [(map->Ballot {::choice "a"}) (map->Ballot {}) (rec/seal (map->Ballot {::choice "a"}))]
          [sel want] [[::typo :recognitum/unknown-name] [::amount :recognitum/unknown-name]
                      [42 :recognitum/not-a-selection]]]
    (is (= [want []] (outcome #(rec/proves? x sel))) (pr-str x sel))))

(deftest seal-of-a-sealed-value-reads-its-selection
  (let [v (map->Payment {::amount 50})]
    (doseq [[sel want] unknown]
      (is (= [want []] (outcome #(rec/seal v sel))) (pr-str sel)))
    (doseq [sel [rec/every rec/shape ::amount authorized audit spare spare-int (rec/union)]]
      (is (identical? v (rec/seal v sel)) (pr-str sel)))
    (is (identical? v (rec/seal v)))))

(deftest a-sealed-value-proves-a-concern-its-type-does-not-carry-and-not-another-types-check
  (let [v (map->Payment {::amount 50})]
    (testing "a concern no check of the type carries, and a bundle the type does not bind, are selections"
      (doseq [sel [audit ::audit spare spare-int]]
        (is (true? (rec/proves? v sel)) (pr-str sel))))
    (testing "another type's own check id is an unknown name"
      (is (= :recognitum/unknown-name (first (outcome #(rec/proves? v ::n)))))
      (is (= :recognitum/unknown-name (first (outcome #(rec/seal v ::n))))))))

(deftest a-draft-holding-an-undeclared-key-proves-nothing-until-the-key-is-gone
  (let [d (into (rec/draft Payment) {::amount 50 :admin? true})
        sels [rec/every authorized ::authorized ::amount ::under-limit rec/shape (rec/union)]]
    (is (true? (rec/check d rec/every)) "check is unchanged: every check passes")
    (let [memory (rec/proven-checks d)]
      (is (= #{::amount ::under-limit} memory))
      (doseq [sel sels]
        (is (false? (rec/proves? d sel)) (pr-str sel)))
      (is (= memory (rec/proven-checks d)) "the draft's memory is untouched")
      (is (= #{} (rec/proven-concerns d)))
      (is (true? (rec/check d rec/every)))
      (testing "once the key is gone, by clean or by dissoc, proves? answers by the memory, nothing run"
        (doseq [e [(rec/clean d) (dissoc d :admin?)]]
          (is (= [true []] (outcome #(rec/proves? e rec/every))))
          (is (= #{::authorized} (rec/proven-concerns e)))
          (doseq [sel sels]
            (is (true? (rec/proves? e sel)) (pr-str sel))))))
    (testing "an unknown name throws for such a draft too: the selection is read first"
      (is (= :recognitum/unknown-name (first (outcome #(rec/proves? d ::typo))))))))

(deftest the-key-is-known-at-each-write
  (let [d (into (rec/draft Payment) {::amount 50})]
    (rec/check d rec/every)
    (doseq [[label x want]
            [["no undeclared key" d true]
             ["assoc of one" (assoc d :admin? true) false]
             ["assoc of two, one removed" (dissoc (assoc d :admin? true :scratch 1) :admin?) false]
             ["assoc of two, both removed" (dissoc (assoc d :admin? true :scratch 1) :admin? :scratch) true]
             ["merge" (merge d {:admin? true}) false]
             ["merge of the key again" (merge (assoc d :admin? true) {:admin? false}) false]
             ["merge, then dissoc of the key" (dissoc (merge d {:admin? true}) :admin?) true]
             ["dissoc of a declared field while the key is held" (dissoc (assoc d :admin? true ::note "n") ::note) false]
             ["into" (into d {:admin? true}) false]
             ["conj" (conj d [:admin? true]) false]
             ["a write of the key again" (assoc (assoc d :admin? true) :admin? false) false]
             ["the declared optional field" (assoc d ::note "n") true]
             ["a draft under the key" (assoc d :scratch (rec/draft Payment)) false]
             ["with-meta" (with-meta (assoc d :admin? true) {:m 1}) false]
             ["clean" (rec/clean (assoc d :admin? true)) true]]]
      (is (= want (rec/proves? x rec/every)) label))
    (testing "a draft of a sealed value, decorated, with no check called"
      (is (false? (rec/proves? (assoc (rec/draft (map->Payment {::amount 50})) :admin? true) rec/every))))))

(deftest proven-checks-and-proven-concerns-of-a-draft-holding-an-undeclared-key
  (let [d (doto (into (rec/draft Payment) {::amount 50 :admin? true}) (rec/check rec/every))]
    (is (= #{::amount ::under-limit} (rec/proven-checks d)))
    (is (= #{} (rec/proven-concerns d)))
    (is (= #{::authorized} (rec/proven-concerns (rec/clean d))))))

(deftest a-class-and-a-plain-map-prove-nothing-whatever-they-are-asked
  (doseq [x [Payment {::amount 50}], [sel] (cons [rec/every] unknown)]
    (is (false? (rec/proves? x sel)) (pr-str x sel))))
