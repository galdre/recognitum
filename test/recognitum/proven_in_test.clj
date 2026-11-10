(ns recognitum.proven-in-test
  "Values of `defproven-in` types: made and written without checks, carrying what passed, and
  never proven by anything but a run of their checks."
  (:require
   [clojure.edn :as edn]
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]
   [recognitum.proof :as proof]
   [recognitum.proof.key-class :as key-class]
   [recognitum.record :as record])
  (:import
   (recognitum.record Draft Memo)))

(def ^:private log (atom []))

(defn- ran! [id] (swap! log conj id) nil)

(defn- ran [f] (reset! log []) (f) (frequencies @log))

(defprotocol Says (says [v]))

(rec/defproven-in Ballot [a b ^:optional c]
  rec/checks
  (a [] (ran! ::a) (int? a))
  (b [] (ran! ::b) (int? b))
  (c [] (ran! ::c) (int? c))
  (b-not-below-a [] (ran! ::b-not-below-a) (>= b a))
  Says
  (says [this] [a b]))

(rec/defproven Box [item]
  rec/checks
  (item [] (some? item)))

(rec/defproven-in Shelf [held]
  rec/checks
  (held [] (ran! ::held) (some? held)))

(def ^:private selections [rec/every rec/shape rec/pure ::a ::b ::c ::b-not-below-a (rec/reading ::b)])

(defn- proves-nothing? [x]
  (and (not (rec/sealed? x))
       (not-any? #(rec/proves? x %) selections)
       (empty? (rec/proven-checks x))
       (empty? (rec/proven-concerns x))))

(defn- memory [v] (proof/memory key-class/strategy v))

(defn- err [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest a-value-is-made-without-checks-and-proves-nothing
  (doseq [v [(map->Ballot {::a 0 ::b 1}) (->Ballot 0 1 nil) (assoc (map->Ballot {::a 0}) ::b 1)
             (edn/read-string {:readers (rec/data-readers)} (pr-str (map->Ballot {::a 0 ::b 1})))]]
    (is (proves-nothing? v))
    (is (= 0 (::a v)))
    (is (= [0 1] (says v)))))

(deftest a-seal-runs-what-is-unsettled-writes-in-place-and-returns-the-value
  (let [v (map->Ballot {::a 0 ::b 1})]
    (is (= {::a 1 ::b 1 ::b-not-below-a 1} (ran #(is (identical? v (rec/seal v))))))
    (is (rec/proves? v rec/every))
    (is (not (rec/sealed? v)))
    (is (= {} (ran #(rec/seal v rec/every))))
    (is (= {::b-not-below-a 1} (ran #(rec/recheck v ::b-not-below-a))))))

(deftest a-seal-with-a-selection-runs-it-and-the-floor
  (let [v (map->Ballot {::a 0 ::b 1 ::c 2})]
    (is (= {::a 1 ::b 1 ::c 1} (ran #(rec/seal v ::a))))
    (is (rec/proves? v ::a))
    (is (not (rec/proves? v rec/every)))))

(deftest a-failed-seal-keeps-what-passed-and-forgets-what-failed
  (let [v (map->Ballot {::a 3 ::b 1})
        e (err #(rec/seal v))]
    (is (= :recognitum/check-failed (:error e)))
    (is (= #{::b-not-below-a} (set (keys (:failed e)))))
    (is (= #{::a ::b ::c} (rec/proven-checks v)))))

(deftest a-write-forgets-the-readers-of-what-it-changes
  (let [v (map->Ballot {::a 0 ::b 1})]
    (rec/seal v)
    (is (= #{::a ::c} (rec/proven-checks (assoc v ::b 2))))
    (is (= #{::a ::c} (rec/proven-checks (assoc v ::b 1N))))
    (is (identical? v (assoc v ::b (::b v))))
    (is (= (rec/proven-checks v) (rec/proven-checks (with-meta v {:m 1}))))
    (is (= :recognitum/undeclared-keys (:error (err #(assoc v ::z 1)))))))

(deftest a-write-that-removes-a-key-and-adds-another-forgets-the-readers-of-both
  (let [v (map->Ballot {::a 0})]
    (rec/check v ::a)
    (is (contains? (rec/proven-checks v) ::a))
    (let [w (persistent! (-> (transient v) (dissoc! ::a) (assoc! ::c 2)))]
      (is (= {::c 2} (into {} w)))
      (is (not (contains? (rec/proven-checks w) ::a))))))

(deftest a-check-in-place-is-seen-by-every-holder
  (let [v (map->Ballot {::a 0 ::b 1})
        held {:v v}]
    (rec/check v ::b-not-below-a)
    (is (rec/proves? (:v held) ::b-not-below-a))))

(deftest a-hand-built-memory-proves-nothing
  (let [type (record/type-of Ballot)]
    (testing "a value as its own proof, which shows every check of a sealed type"
      (let [v (map->Ballot {::a 0 ::b 1})]
        (reset! (memory v) (Memo. type v (:ids type) #{} v nil))
        (is (proves-nothing? v))
        (is (= {::a 1 ::b 1 ::b-not-below-a 1} (ran #(rec/seal v))))))
    (testing "a sealed value of another type as the proof"
      (let [v (map->Ballot {::a 0 ::b 1})
            b (map->Box {::item 1})]
        (reset! (memory v) (Memo. type b (:ids type) #{} b nil))
        (is (proves-nothing? v))))
    (testing "another value's marked proof, claimed for this one's entries"
      (let [donor (map->Ballot {::a 0 ::b 1})
            _ (rec/seal donor)
            ^Memo m @(memory donor)
            v (map->Ballot {::a 3 ::b 1})]
        (reset! (memory v) (Memo. type v (.-passes m) #{} (.-proof m) (.-mask m)))
        (is (proves-nothing? v))
        (is (not (rec/sealed? (.-proof m))))
        (is (not (rec/proves? (.-proof m) rec/every)))))
    (testing "another value's memory, moved onto other entries"
      (let [donor (map->Ballot {::a 0 ::b 1})
            _ (rec/seal donor)
            v (map->Ballot {::a 7 ::b 9})]
        (reset! (memory v) @(memory donor))
        (is (proves-nothing? v))))
    (testing "a draft's memory"
      (let [v (map->Ballot {::a 0 ::b 1})]
        (reset! (memory v) @(.-cell ^Draft (rec/draft (map->Box {::item 1}))))
        (is (proves-nothing? v))))))

(deftest the-type-has-no-drafts
  (let [v (map->Ballot {::a 0 ::b 1})
        called (atom false)]
    (doseq [f [#(rec/draft Ballot) #(rec/draft v) #(rec/clean v) #(rec/drafting v (fn [x] (reset! called true) x))]]
      (let [e (err f)]
        (is (= :recognitum/no-drafts (:error e)))))
    (is (not @called))
    (is (.contains (ex-message (try (rec/draft Ballot) (catch Exception e e))) "map->Ballot"))))

(deftest a-draft-seals-against-every-check-only
  (let [d (assoc (rec/draft Box) ::item 1)]
    (is (= :recognitum/draft-selection (:error (err #(rec/seal d ::item)))))
    (is (empty? (rec/proven-checks d)))
    (is (rec/sealed? (rec/seal d rec/every)))))

(deftest batched-runs-write-each-value
  (let [v (map->Ballot {::a 0 ::b 1})
        w (map->Ballot {::a 3 ::b 1})
        d (assoc (rec/draft Box) ::item 1)]
    (is (= [true false true] (mapv true? (rec/check-all [v w d] rec/every))))
    (is (rec/proves? v rec/every))
    (is (not (contains? (rec/proven-checks w) ::b-not-below-a)))
    (is (= {::b-not-below-a 2} (ran #(rec/recheck-all [v w] ::b-not-below-a))))))

(deftest seal-all-enters-values-and-drafting-all-ignores-them
  (testing "a value holding no draft comes back itself, sealed against the selection"
    (let [v (map->Ballot {::a 0 ::b 1})
          out (rec/seal-all {:x [v]} ::a)]
      (is (identical? v (get-in out [:x 0])))
      (is (rec/proves? v ::a))
      (is (not (rec/proves? v rec/every)))))
  (testing "a value holding a draft comes back new, forgetting the field's readers"
    (let [v (map->Shelf {::held [(assoc (rec/draft Box) ::item 1)]})
          _ (rec/check v ::held)
          out (rec/seal-all [v])]
      (is (not (identical? v (first out))))
      (is (rec/sealed? (first (::held (first out)))))
      (is (= {::held 1} (ran #(rec/seal-all [(map->Shelf {::held [(assoc (rec/draft Box) ::item 1)]})]))))
      (is (rec/proves? (first out) rec/every))))
  (testing "drafting-all neither opens, nor enters, nor seals a value"
    (let [d (assoc (rec/draft Box) ::item 1)
          v (map->Ballot {::a 0 ::b 1 ::c d})
          out (rec/drafting-all [v] identity)]
      (is (identical? v (first out)))
      (is (rec/draft? (::c (first out))))
      (is (empty? (rec/proven-checks v))))))

(deftest nothing-a-strategy-holds-for-a-type-counts-as-sealed
  (let [v (map->Ballot {::a 0 ::b 1})
        g (proof/gate-of Ballot)]
    (rec/seal v)
    (is (false? (g ::record/sealed? v nil)))
    (is (identical? v (g ::record/seal v #{::a})))
    (is (= :recognitum/no-drafts (:error (err #(g ::record/draft-of v nil)))))
    (let [d (assoc (rec/draft Box) ::item 1)]
      (rec/check d ::item)
      (is (not (rec/sealed? (.-proof ^Memo @(.-cell ^Draft d)))))
      (is (not (rec/proves? (.-proof ^Memo @(.-cell ^Draft d)) rec/every))))))

(deftest a-displaced-value-reads-and-refuses-the-rest
  (let [form '(recognitum.core/defproven-in Moved [a] recognitum.core/checks (a [] (int? a)))
        _ (binding [*ns* (the-ns 'recognitum.proven-in-test)] (eval form))
        make (fn [m] (@(ns-resolve 'recognitum.proven-in-test 'map->Moved) m))
        v (make {::a 1})
        _ (rec/seal v)
        _ (binding [*ns* (the-ns 'recognitum.proven-in-test)] (eval form))
        names? (fn [f] (.contains (str (ex-message (try (f) (catch Exception e e)))) "map->Moved"))]
    (is (= 1 (::a v)))
    (is (proves-nothing? v))
    (is (every? names? [#(assoc v ::a 2) #(rec/seal v) #(rec/check v rec/every) #(rec/recheck v rec/every)
                        #(rec/check-all [v] rec/every) #(rec/recheck-all [v] rec/every)]))
    (is (rec/proves? (rec/seal (make (into {} v))) rec/every))
    (testing "and stays refused by draft when its name is defined sealed"
      (binding [*ns* (the-ns 'recognitum.proven-in-test)]
        (eval '(recognitum.core/defproven Moved [a] recognitum.core/checks (a [] (int? a)))))
      (is (= :recognitum/no-drafts (:error (err #(rec/draft v))))))))

(deftest seal-all-lists-a-displaced-value-among-its-failures
  (let [form '(recognitum.core/defproven-in Stale [a] recognitum.core/checks (a [] (some? a)))
        _ (binding [*ns* (the-ns 'recognitum.proven-in-test)] (eval form))
        make (fn [m] (@(ns-resolve 'recognitum.proven-in-test 'map->Stale) m))
        bare (make {::a 1})
        holding (make {::a [(assoc (rec/draft Box) ::item 1)]})
        _ (binding [*ns* (the-ns 'recognitum.proven-in-test)] (eval form))
        good (map->Ballot {::a 0 ::b 1})
        data (err #(rec/seal-all [bare holding good]))]
    (is (= :recognitum/drafts-failed (:error data)))
    (is (= #{[0] [1]} (set (keys (:failures data)))))
    (is (every? #(= :recognitum/displaced (:error %)) (vals (:failures data))))
    (is (identical? bare (first (:drafts data))))
    (is (identical? holding (second (:drafts data))))
    (is (proves-nothing? bare))
    (is (proves-nothing? holding))))

(deftest a-type-given-where-a-value-belongs-is-refused
  (doseq [[t n] [[Box 'recognitum.proven-in-test/Box] [Ballot 'recognitum.proven-in-test/Ballot]]
          x [t (record/type-of t)]
          f [#(rec/check x rec/every) #(rec/recheck x rec/every) #(rec/seal x) #(rec/seal x rec/every)
             #(rec/check-all [x] rec/every) #(rec/recheck-all [x] rec/every)
             #(rec/proven-checks x) #(rec/proven-concerns x) #(rec/clean x) #(rec/drafting x identity)]]
    (is (= [(str "a type was given where a value belongs: " n) {:error :recognitum/not-a-value :type n}]
           (try (f) nil (catch clojure.lang.ExceptionInfo e [(ex-message e) (ex-data e)])))
        (str n (when (map? x) "'s type map"))))
  (testing "proves? answers false for a type's class and its type map"
    (doseq [t [Box Ballot], x [t (record/type-of t)]]
      (is (false? (rec/proves? x rec/every)))))
  (testing "draft opens a type's class, and refuses its type map"
    (is (rec/draft? (rec/draft Box)))
    (is (= :recognitum/not-a-value (:error (err #(rec/draft (record/type-of Box))))))
    (is (= :recognitum/not-a-value (:error (err #(rec/draft (record/type-of Ballot)))))))
  (testing "a value among others in a batch"
    (is (= :recognitum/not-a-value
           (:error (err #(rec/check-all [(map->Ballot {::a 0 ::b 1}) Box] rec/every)))))))
