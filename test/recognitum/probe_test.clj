(ns recognitum.probe-test
  "A required field's presence as a check; probe and probe-all, their overrides and what they
  leave behind; seal-all and drafting-all over values of displaced definitions."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(def ^:private calls
  "The keys `on-file` was asked, one entry per call."
  (atom []))

(defn on-file
  "A source: whether each key is on file; 0 and 7 are."
  [ks]
  (swap! calls conj (vec ks))
  (into {} (map (fn [k] [k (contains? #{0 7} k)])) ks))

(defn- answering
  "An override that answers `x` for every key, counting its calls in `n`."
  [x n]
  (fn [ks] (swap! n inc) (zipmap ks (repeat x))))

(rec/defconcern shapes "The shape checks of Shaped.")

(rec/defproven Shaped [u]
  rec/checks
  (u [] shapes (int? u)))

(rec/defproven Item [a b ^:optional c]
  rec/checks
  (a [] (int? a))
  (known [a] (true? (rec/fetch on-file a))))

(rec/defproven Note [u note]
  rec/checks
  (u [] (int? u)))

(rec/defproven-in Loose [u note]
  rec/checks
  (u [] (int? u)))

(rec/defproven Holder [x]
  rec/checks
  (x [] (some? x)))

(defn- of [t m] (into (rec/draft t) m))

;;; ------------------------------------------------------------------ presence is a check

(deftest a-run-of-every-reports-absent-required-fields
  (let [lacking {:failed {} :blocked #{} :missing #{::note}}]
    (testing "a report even where every check passes"
      (is (= lacking (rec/check (of Note {::u 1}) rec/every)))
      (is (= lacking (rec/recheck (of Note {::u 1}) rec/every)))
      (is (= [lacking true] (rec/check-all [(of Note {::u 1}) (of Note {::u 1 ::note "n"})] rec/every)))
      (is (= [lacking] (rec/recheck-all [(of Note {::u 1})] rec/every))))
    (testing "beside a failed check"
      (is (= #{::note} (:missing (rec/check (of Note {::u :x}) rec/every))))
      (is (contains? (:failed (rec/check (of Note {::u :x}) rec/every)) ::u)))
    (testing "a draft whose every check is remembered still reports it"
      (let [d (of Note {::u 1})]
        (rec/check d ::u)
        (is (= lacking (rec/check d rec/every)))
        (is (= [lacking] (rec/check-all [d] rec/every)))))
    (testing "a selection that does not ask the field's presence does not report it"
      (is (true? (rec/check (of Note {::u 1}) ::u)))
      (is (true? (rec/check (of Note {::u 1}) (rec/union))))
      (is (true? (rec/recheck (of Note {::u 1}) ::u)))
      (is (= [true] (rec/check-all [(of Note {::u 1})] (rec/reading ::u)))))
    (testing "nor a sealed value, which holds every required field"
      (is (true? (rec/check (map->Note {::u 1 ::note "n"}) rec/every))))
    (testing "a value of a defproven-in type, as a draft"
      (is (= lacking (rec/check (map->Loose {::u 1}) rec/every))))))

(deftest a-selection-asks-a-presence-where-it-asks-the-field-s-shape
  (let [asks (fn [sel m] (:missing (rec/check (of Note m) sel) #{}))]
    (doseq [[label sel want] [["every" rec/every #{::u ::note}]
                              ["shape" rec/shape #{::u ::note}]
                              ["pure" rec/pure #{::u ::note}]
                              ["reading note" (rec/reading ::note) #{::note}]
                              ["reading u" (rec/reading ::u) #{::u}]
                              ["the name of u's shape check" ::u #{::u}]
                              ["none" (rec/union) #{}]
                              ["a union" (rec/union (rec/reading ::note) ::u) #{::u ::note}]
                              ["every except a name, which removes no presence" (rec/except rec/every ::u) #{::u ::note}]
                              ["shape except reading note" (rec/except rec/shape (rec/reading ::note)) #{::u}]
                              ["every except reading u" (rec/except rec/every (rec/reading ::u)) #{::note}]]]
      (testing label
        (is (= want (asks sel {})) "check")
        (is (= want (:missing (rec/recheck (of Note {}) sel) #{})) "recheck")
        (is (= want (:missing (first (rec/check-all [(of Note {})] sel)) #{})) "check-all")
        (is (= want (:missing (first (rec/recheck-all [(of Note {})] sel)) #{})) "recheck-all")
        (is (= want (:missing (rec/probe Note {} sel) #{})) "probe")
        (is (= want (:missing (first (rec/probe-all Note [{}] sel)) #{})) "probe-all")
        (is (= (disj want ::u) (asks sel {::u 1})) "only what is absent"))))
  (testing "through the waits of a selected check: a check that reads a field asks its presence"
    (is (= #{::a} (:missing (rec/check (of Item {}) ::known))))
    (is (= #{::a} (:missing (rec/probe Item {} ::known))))
    (is (= #{::a} (:missing (rec/check (of Item {}) (rec/fetching on-file))))))
  (testing "a concern holding a shape check asks its field's presence"
    (is (= #{::u} (:missing (rec/check (of Shaped {}) shapes)))))
  (testing "a name in an except removes no presence, whether a keyword, a concern or a check's var"
    (doseq [nm [::u shapes :recognitum.probe-test/shapes]]
      (is (= #{::u} (:missing (rec/check (of Shaped {}) (rec/except rec/shape nm)))) (pr-str nm)))))

(rec/defproven Pair [a b]
  rec/checks
  (a-not-above-b [] (<= a b)))

(rec/defconcern tee-shape "The shape checks of Tee.")

(rec/defproven Tee [a b ^:optional c]
  rec/checks
  (a [] tee-shape (int? a))
  (b [] tee-shape (int? b))
  (c [] tee-shape (int? c))
  (b-not-below-a [a b] (>= b a))
  (a-small [a] (< a 5)))

(defn- missing-by-each-run
  "What each of check, recheck, check-all, recheck-all, probe and probe-all reports missing on
  `m`, a map of `t`'s fields, with `sel`."
  [t m sel]
  {:check (:missing (rec/check (of t m) sel) #{})
   :recheck (:missing (rec/recheck (of t m) sel) #{})
   :check-all (:missing (first (rec/check-all [(of t m)] sel)) #{})
   :recheck-all (:missing (first (rec/recheck-all [(of t m)] sel)) #{})
   :probe (:missing (rec/probe t m sel) #{})
   :probe-all (:missing (first (rec/probe-all t [m] sel)) #{})})

(deftest a-presence-check-is-selected-as-any-check
  (let [each (fn [want] (zipmap [:check :recheck :check-all :recheck-all :probe :probe-all] (repeat want)))]
    (testing "an except that removes the checks reading b keeps a's presence check"
      (is (= (each #{::a}) (missing-by-each-run Pair {::b 1} (rec/except rec/every (rec/reading ::b))))))
    (doseq [[label sel want]
            [["a name less itself selects nothing" (rec/except ::a-small ::a-small) #{}]
             ["a concern less a name: b's shape check is left, waiting on b's presence"
              (rec/except ::tee-shape ::a) #{::b}]
             ["reading b less a name: b's shape check and presence check are left"
              (rec/except (rec/reading ::b) ::b-not-below-a) #{::b}]
             ["a nested except takes away what it selects"
              (rec/except rec/every (rec/except (rec/reading ::b) ::b-not-below-a)) #{::a ::b}]
             ["every less shape: what is left waits on the presence checks of what it reads"
              (rec/except rec/every rec/shape) #{::a ::b}]]]
      (testing label
        (is (= (each want) (missing-by-each-run Tee {} sel)))))
    (testing "every less shape leaves no presence check where no other check reads a field"
      (is (= (each #{}) (missing-by-each-run Note {} (rec/except rec/every rec/shape))))
      (is (true? (rec/check (of Note {}) (rec/except rec/every rec/shape)))))
    (testing "a presence check is never listed as pulled back"
      (let [r (rec/check (of Tee {::a :x}) (rec/except rec/every ::a ::a-small))]
        (is (= #{::b} (:missing r)))
        (is (= #{::a} (set (keys (:pulled-back r)))))))))

(deftest a-check-true-on-the-shape-is-followed-by-proves-true
  (testing "a draft"
    (doseq [m [{::u 1} {::u 1 ::note "n"} {} {::note "n"}]
            sel [rec/every rec/shape (rec/union (rec/reading ::note) ::u)]]
      (let [d (of Note m)]
        (when (true? (rec/check d sel))
          (is (true? (rec/proves? d sel)) (pr-str m sel))))))
  (testing "rec/shape on a draft lacking a field no check reads reports it, and proves? stays false"
    (let [d (of Note {::u 1})]
      (is (= {:failed {} :blocked #{} :missing #{::note}} (rec/check d rec/shape)))
      (is (false? (rec/proves? d rec/shape)))))
  (testing "a value of a defproven-in type"
    (let [v (map->Loose {::u 1})]
      (is (= #{::note} (:missing (rec/check v rec/shape))))
      (is (false? (rec/proves? v rec/shape))))
    (let [v (map->Loose {::u 1 ::note "n"})]
      (is (true? (rec/check v rec/shape)))
      (is (true? (rec/proves? v rec/shape)))))
  (testing "a narrower check true while a field it does not ask is absent: proves? is false"
    (let [d (of Note {::u 1})]
      (is (true? (rec/check d ::u)))
      (is (false? (rec/proves? d ::u))))))

(rec/defproven Spare [^:optional x]
  rec/checks
  (x [] (int? x)))

(deftest a-type-with-no-required-field-reports-none-absent
  (let [d (rec/draft Spare)]
    (is (true? (rec/check d rec/every)))
    (is (= [true] (rec/check-all [d] rec/every)))
    (is (true? (rec/proves? d rec/every)))
    (is (true? (rec/probe Spare {})))))

(deftest proves-is-false-while-a-required-field-is-absent
  (let [d (doto (of Note {::u 1}) (rec/check rec/every))]
    (is (= #{::u} (rec/proven-checks d)) "the memory lists checks only")
    (doseq [sel [rec/every ::u rec/shape (rec/union)]]
      (is (false? (rec/proves? d sel))))
    (is (true? (rec/proves? (assoc d ::note "n") ::u))))
  (let [v (doto (map->Loose {::u 1}) (rec/check rec/every))]
    (is (false? (rec/proves? v ::u)))))

(deftest one-seal-error-for-every-combination
  (let [shape (fn [d] (select-keys d [:error :type :failed :missing]))
        failed-u {::u {:data false :blocked #{}}}]
    (doseq [[label m want]
            [["only a field absent" {::u 1} {:failed {} :missing #{::note}}]
             ["a check failed and a field absent" {::u :x} {:failed failed-u :missing #{::note}}]
             ["only a check failed" {::u :x ::note "n"} {:failed failed-u}]
             ["every field absent" {} {:failed {::u {:data {:absent ::u} :blocked #{}}} :missing #{::u ::note}}]]]
      (let [want (assoc want :error :recognitum/check-failed :type 'recognitum.probe-test/Note)]
        (testing label
          (is (= want (shape (err #(rec/seal (of Note m))))) "seal")
          (is (= want (shape (err #(map->Note m)))) "the constructor")
          (is (= want (shape (get-in (err #(rec/seal-all [(of Note m)])) [:failures [0]]))) "seal-all")
          (is (= want (shape (get-in (err #(rec/drafting-all [(map->Note {::u 1 ::note "n"})]
                                                             (fn [[d]] [(reduce dissoc (into d m) (remove (set (keys m)) [::u ::note]))])))
                                     [:failures [0]])))
              "drafting-all"))))
    (testing "a write that removes a field"
      (is (= {:error :recognitum/check-failed :type 'recognitum.probe-test/Note :failed {} :missing #{::note}}
             (shape (err #(dissoc (map->Note {::u 1 ::note "n"}) ::note))))))
    (testing "a value of a defproven-in type"
      (is (= {:error :recognitum/check-failed :type 'recognitum.probe-test/Loose :failed {} :missing #{::note}}
             (shape (err #(rec/seal (map->Loose {::u 1}))))))
      (is (= {:error :recognitum/check-failed :type 'recognitum.probe-test/Loose :failed {} :missing #{::note}}
             (shape (err #(rec/seal (map->Loose {::u 1}) ::u))))))
    (testing "the seal runs its checks whatever is absent, and remembers what passed"
      (let [d (of Note {::u 1})]
        (err #(rec/seal d))
        (is (= #{::u} (rec/proven-checks d)))))
    (testing "an undeclared key is refused before any check runs, as before"
      (is (= :recognitum/undeclared-keys (:error (err #(rec/seal (of Note {::z 1})))))))))

;;; ------------------------------------------------------------------ probing

(deftest probe-answers-as-check-on-a-fresh-draft
  (reset! calls [])
  (is (true? (rec/probe Item {::a 0 ::b 1})))
  (is (= {:failed {} :blocked #{} :undeclared #{::z}} (rec/probe Item {::a 0 ::b 1 ::z 2}))
      "an undeclared key makes a report, and the checks still run")
  (is (= #{::b} (:missing (rec/probe Item {::a 0}))))
  (is (= #{::known} (set (keys (:failed (rec/probe Item {::a 1 ::b 1}))))))
  (testing "a selection other than every reports no absent field"
    (is (true? (rec/probe Item {::a 0} ::a)))
    (is (true? (rec/probe Item {} (rec/union)))))
  (testing "with every, true exactly where a seal seals"
    (doseq [m [{::a 0 ::b 1} {::a 1 ::b 1} {::a 0} {} {::a :x ::b 1}]]
      (is (= (rec/probe Item m)
             (rec/check (of Item m) rec/every))))))

(deftest probe-reads-any-map-and-leaves-it-as-it-was
  (let [d (doto (of Item {::a 1 ::b 1}) (rec/check rec/every))
        before (rec/proven-checks d)
        v (rec/seal (of Item {::a 0 ::b 1}))
        n (atom 0)
        flip {on-file (answering true n)}]
    (testing "a draft: its entries now, not its memory"
      (is (true? (rec/probe Item d rec/every flip)))
      (is (= before (rec/proven-checks d)))
      (is (= (rec/probe Item (into {} d)) (rec/probe Item d))))
    (testing "a sealed value stays sealed and remembers nothing new"
      (is (= {:failed {::known {:data false :blocked #{}}} :blocked #{}}
             (rec/probe Item v rec/every {on-file (answering false n)})))
      (is (rec/sealed? v))
      (is (rec/proves? (rec/draft v) rec/every)))
    (testing "a record, and a draft or value of another type"
      (is (= {:failed {::a {:data {:absent ::a} :blocked #{}}} :blocked #{} :missing #{::a} :undeclared #{::x}}
             (rec/probe Item (map->Holder {::x 0}) ::a))
          "a sealed value of another type: its fields are undeclared, and its checks are not run")
      (is (= #{::x} (:undeclared (rec/probe Item (of Holder {::x 0 ::a 0 ::b 1})))))
      (is (= #{::u ::note} (:undeclared (rec/probe Item (map->Note {::u 1 ::note "n"}))))))
    (testing "a fresh draft made after a probe under an override remembers nothing"
      (is (= #{} (rec/proven-checks (of Item {::a 1 ::b 1}))))
      (is (= :recognitum/check-failed (:error (err #(rec/seal (of Item {::a 1 ::b 1})))))))))

(deftest an-override-replaces-the-source-for-the-call-only
  (let [n (atom 0)]
    (reset! calls [])
    (is (true? (rec/probe Item {::a 1 ::b 1} rec/every {on-file (answering true n)})))
    (is (= 1 @n))
    (is (= [] @calls) "the source is not called")
    (is (= #{::known} (set (keys (:failed (rec/probe Item {::a 1 ::b 1}))))))
    (is (= [[1]] @calls) "the next probe reads the source")
    (testing "an empty map overrides nothing"
      (is (= (rec/probe Item {::a 1 ::b 1}) (rec/probe Item {::a 1 ::b 1} rec/every {}))))))

(deftest an-override-is-not-seen-by-a-run-on-another-thread
  (let [asked (promise) release (promise)
        override {on-file (fn [ks] (deliver asked true) (deref release 5000 nil) (zipmap ks (repeat true)))}
        paused (future (rec/probe Item {::a 1 ::b 1} rec/every override))]
    (try
      (is (deref asked 5000 false))
      (reset! calls [])
      (is (= #{::known} (set (keys (:failed (rec/check (of Item {::a 1 ::b 1}) rec/every))))))
      (is (= [[1]] @calls))
      (is (false? (rec/sealed? (try (rec/seal (of Item {::a 1 ::b 1})) (catch Exception _ nil)))))
      (finally (deliver release true)))
    (is (true? (deref paused 5000 ::timed-out)))))

(def ^:private inner (atom nil))

(rec/defproven Outer [y]
  rec/checks
  (y [] (do (reset! inner [(rec/check (of Item {::a 1 ::b 1}) rec/every)
                           (rec/probe Item {::a 1 ::b 1})])
            (true? (rec/fetch on-file y)))))

(deftest an-override-is-not-seen-by-a-run-a-check-starts-inside-the-probe
  (let [n (atom 0)]
    (is (true? (rec/probe Outer {::y 1} rec/every {on-file (answering true n)})))
    (is (= #{::known} (set (keys (:failed (first @inner))))) "the inner check read the source itself")
    (is (= #{::known} (set (keys (:failed (second @inner))))) "and so did a probe without overrides")
    (is (= 1 @n))))

(deftest probe-all-is-probe-of-each-in-one-run
  (let [ms [{::a 0 ::b 1} {::a 1 ::b 1} {::a 7 ::b 9} {::a 0}]]
    (reset! calls [])
    (is (= (mapv #(rec/probe Item %) ms) (rec/probe-all Item ms)))
    (reset! calls [])
    (rec/probe-all Item ms)
    (is (= 1 (count @calls)) "one call of the source for every map")
    (let [n (atom 0)]
      (rec/probe-all Item ms rec/every {on-file (answering false n)})
      (is (= 1 @n)))
    (is (= [] (rec/probe-all Item [])))))

(deftest probe-refuses-what-is-not-a-class-or-a-map
  (is (= :recognitum/not-a-type (:error (err #(rec/probe (of Item {}) {})))))
  (is (= :recognitum/not-a-type (:error (err #(rec/probe String {})))))
  (is (= :recognitum/not-a-map (:error (err #(rec/probe Item [1 2])))))
  (testing "a class of a displaced definition"
    (let [old (binding [*ns* (the-ns 'recognitum.probe-test)]
                (eval '(recognitum.core/defproven Gone [a] recognitum.core/checks (a [] (int? a)))))
          _ (binding [*ns* (the-ns 'recognitum.probe-test)]
              (eval '(recognitum.core/defproven Gone [a] recognitum.core/checks (a [] (int? a)))))]
      (is (= :recognitum/displaced-constructor (:error (err #(rec/probe old {::a 1})))))
      (is (true? (rec/probe (ns-resolve 'recognitum.probe-test 'Gone) {::a 1}))))))

;;; ------------------------------------------------------------------ displaced values in seal-all

(rec/defproven Pack [item code]
  rec/checks
  (code [] (true? (rec/fetch on-file code))))

(deftest a-value-a-draft-holds-leaves-the-draft-at-its-level
  (testing "a draft holding a value the walk does not enter is checked with the drafts holding none"
    (let [form '(recognitum.core/defproven Gone2 [a] recognitum.core/checks (a [] (int? a)))
          _ (binding [*ns* (the-ns 'recognitum.probe-test)] (eval form))
          old (@(ns-resolve 'recognitum.probe-test 'map->Gone2) {::a 1})
          _ (binding [*ns* (the-ns 'recognitum.probe-test)] (eval form))
          sealed (map->Holder {::x 1})]
      (reset! calls [])
      (rec/seal-all [(of Pack {::item sealed ::code 0}) (of Pack {::item 1 ::code 7})])
      (is (= 1 (count @calls)) "a sealed value")
      (reset! calls [])
      (is (= #{[0 ::item]} (set (keys (:failures (err #(rec/seal-all [(of Pack {::item old ::code 0})
                                                                      (of Pack {::item 1 ::code 7})])))))))
      (is (= 1 (count @calls)) "a value of a displaced definition")
      (reset! calls [])
      (rec/drafting-all [(of Pack {::item (map->Loose {::u 1}) ::code 0}) (of Pack {::item 1 ::code 7})] identity)
      (is (= 1 (count @calls)) "a value of a defproven-in type, which drafting-all does not enter"))))

(defn- define! [form]
  (binding [*ns* (the-ns 'recognitum.probe-test)] (eval form)))

(deftest seal-all-reports-a-displaced-value-of-each-kind
  (let [sealed '(recognitum.core/defproven Old [a] recognitum.core/checks (a [] (int? a)))
        unsealed '(recognitum.core/defproven-in OldIn [a] recognitum.core/checks (a [] (int? a)))
        mk (fn [n m] (@(ns-resolve 'recognitum.probe-test n) m))
        _ (define! sealed) _ (define! unsealed)
        v (mk 'map->Old {::a 1})
        w (mk 'map->OldIn {::a 1})
        d (of (ns-resolve 'recognitum.probe-test 'Old) {::a 1})
        _ (define! sealed) _ (define! unsealed)
        good (of Holder {::x 1})
        data (err #(rec/seal-all [v {:in w} d good #{v}]))]
    (is (= :recognitum/drafts-failed (:error data)))
    (is (= {[0] :recognitum/displaced [1 :in] :recognitum/displaced [2] :recognitum/displaced-constructor
            [4 v] :recognitum/displaced}
           (update-vals (:failures data) :error)))
    (is (identical? v (first (:drafts data))))
    (is (identical? w (:in (second (:drafts data)))))
    (testing "whether or not the name names a current definition"
      (ns-unmap 'recognitum.probe-test 'Old)
      (is (= {[0] :recognitum/displaced} (update-vals (:failures (err #(rec/seal-all [v]))) :error))))
    (testing "inside a draft's field, the draft is checked as it holds it"
      (is (= #{[0 ::x]} (set (keys (:failures (err #(rec/seal-all [(of Holder {::x v})]))))))))))

(deftest drafting-all-opens-a-displaced-value-where-its-name-names-a-definition
  (let [form '(recognitum.core/defproven Moved [a] recognitum.core/checks (a [] (int? a)))
        _ (define! form)
        v (@(ns-resolve 'recognitum.probe-test 'map->Moved) {::a 1})
        _ (define! form)
        got (atom nil)]
    (testing "redefined: opened as draft opens it, and sealed against the current definition"
      (let [[x] (rec/drafting-all [v] (fn [s] (reset! got (first s)) s))]
        (is (rec/draft? @got))
        (is (rec/sealed? x))
        (is (= {::a 1} (into {} x)))))
    (testing "unmapped: f gets it as it is, and the seal reports it"
      (ns-unmap 'recognitum.probe-test 'Moved)
      (let [data (err #(rec/drafting-all [v (of Holder {::x 1})] (fn [s] (reset! got (first s)) s)))]
        (is (identical? v @got))
        (is (= {[0] :recognitum/displaced} (update-vals (:failures data) :error)))
        (is (identical? v (first (:drafts data))))))))
