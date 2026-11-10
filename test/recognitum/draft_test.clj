(ns recognitum.draft-test
  "Drafts: what they accept, what they remember, and what seal runs because of it."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]
   [demo.heist :as h]
   [demo.house :as house]
   [recognitum.record :as record])
  (:import
   (demo.heist Heist)
   (recognitum.record Draft Memo)))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(def ^:private entries
  {::h/name "The Italian Job" ::h/crew #{"Charlie" "Stella" "Lyle"} ::h/take 3000
   ::h/cuts {"Charlie" 1000 "Stella" 1000 "Lyle" 1000}})

(deftest a-draft-of-the-type-holds-and-passes-nothing
  (let [d (rec/draft Heist)]
    (is (rec/draft? d))
    (is (= 0 (count d)))
    (is (= #{} (rec/proven-checks d)))
    (is (not (rec/proves? d rec/every)))))

(deftest nil-is-neither-sealed-nor-a-draft
  (is (false? (rec/sealed? nil)))
  (is (false? (rec/draft? nil)))
  (is (false? (rec/proves? nil rec/every))))

(deftest a-sorted-map-is-neither-sealed-nor-a-draft
  (doseq [m [(sorted-map 1 2) (sorted-map-by > 1 2)]]
    (is (false? (rec/sealed? m)))
    (is (false? (rec/draft? m)))
    (is (false? (rec/proves? m rec/every)))))

(deftest a-draft-accepts-any-write
  (let [d (-> (rec/draft Heist) (assoc ::h/take "lots") (assoc :scratch 1))]
    (is (= "lots" (::h/take d)))
    (is (= 1 (:scratch d)))))

(deftest a-draft-of-a-value-passes-everything-and-a-draft-of-a-draft-is-itself
  (let [d (rec/draft h/italian-job)]
    (is (= (rec/checks-of rec/every Heist) (rec/proven-checks d)))
    (is (identical? d (rec/draft d)))
    (testing "sealing it again runs nothing"
      (reset! house/calls [])
      (is (= h/italian-job (rec/seal d)))
      (is (empty? @house/calls)))))

(deftest a-write-forgets-the-checks-that-read-the-key
  (let [d (rec/draft h/italian-job)
        d2 (assoc d ::h/take 3001)]
    (is (= (rec/checks-of rec/every Heist) (rec/proven-checks d)) "the old draft is unchanged")
    (is (= (disj (rec/checks-of rec/every Heist) ::h/take ::h/cuts-sum-to-take)
           (rec/proven-checks d2))
        "only-crew-get-cuts waits on cuts-sum-to-take but does not read take, so it is kept")))

(deftest a-failed-seal-remembers-what-passed
  (let [d (into (rec/draft Heist) (assoc entries ::h/take -1))
        e (err #(rec/seal d))]
    (is (= #{::h/take} (set (keys (:failed e)))))
    (is (= #{::h/cuts-sum-to-take ::h/only-crew-get-cuts} (get-in e [:failed ::h/take :blocked]))
        "directly, and through a check it blocked")
    (is (contains? (rec/proven-checks d) ::h/crew-vetted))
    (testing "the next seal of the mended draft runs only the rest"
      (reset! house/calls [])
      (is (instance? Heist (rec/seal (assoc d ::h/take 3000))))
      (is (empty? @house/calls)))))

(deftest seal-refuses-undeclared-keys-before-running-anything
  (let [d (into (rec/draft Heist) (assoc entries :scratch 1))]
    (reset! house/calls [])
    (is (= {:error :recognitum/undeclared-keys :type 'demo.heist/Heist :keys #{:scratch}}
           (select-keys (err #(rec/seal d)) [:error :type :keys])))
    (is (empty? @house/calls))
    (is (= #{} (rec/proven-checks d)))
    (testing "clean and dissoc remove them"
      (is (instance? Heist (rec/seal (rec/clean d))))
      (is (instance? Heist (rec/seal (dissoc d :scratch)))))))

(deftest check-remembers-and-recheck-reruns
  (let [d (into (rec/draft Heist) entries)]
    (is (true? (rec/check d rec/shape)))
    (is (= (rec/checks-of rec/shape Heist) (rec/proven-checks d)))
    (reset! house/calls [])
    (is (true? (rec/check d ::h/crew-vetted)))
    (is (true? (rec/check d ::h/crew-vetted)))
    (is (= 1 (count @house/calls)) "remembered after the first check")
    (is (true? (rec/recheck d ::h/crew-vetted)))
    (is (= 2 (count @house/calls)) "recheck runs it in any case")))

(deftest marks-moved-onto-other-entries-show-nothing
  (let [d (rec/draft h/italian-job)
        forged (Draft. (assoc entries ::h/take -1) (.-cell ^Draft d) nil)]
    (is (= #{} (rec/proven-checks forged)))
    (is (= :recognitum/check-failed (:error (err #(rec/seal forged)))))))

(deftest a-memory-built-by-hand-around-a-copied-type-map-names-no-type
  ;; The copy claims plain maps as its sealed values, so a memory whose proof is the bad map
  ;; itself would show every check passing; the type's own gate does not answer the copy.
  (let [t (record/type-of Heist)
        copy (assoc t :recognitum.record/class clojure.lang.PersistentArrayMap)
        bad (assoc entries ::h/take -1)
        forged (Draft. bad (atom (Memo. copy bad (:ids t) #{} bad nil)) nil)]
    (is (nil? (:name (record/type-of forged))))
    (is (false? (rec/proves? forged rec/every)))
    (is (= :recognitum/not-a-type (:error (err #(rec/proven-checks forged)))))
    (is (= :recognitum/not-a-type (:error (err #(rec/check-all [forged] rec/every)))))
    (is (= :recognitum/not-a-type (:error (err #(rec/seal forged)))))))

;;; A type whose external check reads a source the tests change under it.

(def ^:private on-file (atom #{0 7}))
(def ^:private hold (atom nil))
(def ^:private source-calls (atom 0))

(defn- files [ks]
  (swap! source-calls inc)
  (let [answer (into {} (for [k ks] [k (contains? @on-file k)]))]
    (when-let [h @hold] (h))
    answer))

(rec/defproven Filed [a b]
  rec/checks
  (a [] (int? a))
  (b [] (int? b))
  (b-not-below-a [] (>= b a))
  (a-known [b-not-below-a] (rec/fetch files a)))

(deftest a-pass-found-before-a-recheck-is-not-written-after-it
  (dotimes [_ 20]
    (reset! on-file #{0 7})
    (let [d (into (rec/draft Filed) {::a 0 ::b 1})
          entered (java.util.concurrent.CountDownLatch. 1)
          release (java.util.concurrent.CountDownLatch. 1)]
      (reset! hold (fn [] (reset! hold nil) (.countDown entered) (.await release 10 java.util.concurrent.TimeUnit/SECONDS)))
      (let [checking (future (rec/check d ::a-known))]
        (is (.await entered 10 java.util.concurrent.TimeUnit/SECONDS) "the check has its yes from the source")
        (reset! on-file #{})
        (is (= #{::a-known} (set (keys (:failed (rec/recheck d ::a-known))))))
        (.countDown release)
        (is (true? @checking))
        (is (not (contains? (rec/proven-checks d) ::a-known))
            "the check's pass, found before the recheck, is not written after it")))))

(deftest recheck-forgets-an-external-check-it-names-even-when-blocked
  (reset! on-file #{0 7})
  (let [d (assoc (rec/draft (map->Filed {::a 0 ::b 1})) ::b -1)]
    (is (contains? (rec/proven-checks d) ::a-known) "writing b keeps the check that reads only a")
    (reset! on-file #{})
    (is (= #{::a-known} (:blocked (rec/recheck d ::a-known))))
    (is (not (contains? (rec/proven-checks d) ::a-known)))
    (testing "the next seal asks the source again"
      (reset! source-calls 0)
      (is (= :recognitum/check-failed (:error (err #(rec/seal (assoc d ::b 1))))))
      (is (= 1 @source-calls))))
  (testing "a recheck that runs it and passes remembers it"
    (reset! on-file #{0 7})
    (let [d (rec/draft (map->Filed {::a 0 ::b 1}))]
      (is (true? (rec/recheck d ::a-known)))
      (is (contains? (rec/proven-checks d) ::a-known)))))

(deftest a-recheck-that-loses-the-race-still-forgets-what-failed
  (dotimes [_ 20]
    (reset! on-file #{0 7})
    (let [d (rec/draft (map->Filed {::a 0 ::b 1}))
          entered (java.util.concurrent.CountDownLatch. 1)
          release (java.util.concurrent.CountDownLatch. 1)]
      (is (contains? (rec/proven-checks d) ::a-known))
      (reset! on-file #{})
      (reset! hold (fn [] (reset! hold nil) (.countDown entered) (.await release 10 java.util.concurrent.TimeUnit/SECONDS)))
      (let [rechecking (future (rec/recheck d ::a-known))]
        (is (.await entered 10 java.util.concurrent.TimeUnit/SECONDS) "the recheck has its no from the source")
        ;; a recheck runs what it names even where it passes, so it writes the memory; a check
        ;; of ::a, which a draft of a sealed value passes, would run and write nothing
        (is (true? (rec/recheck d ::a)) "another run writes the memory meanwhile")
        (.countDown release)
        (is (= #{::a-known} (set (keys (:failed (deref rechecking 10000 nil))))))
        (is (not (contains? (rec/proven-checks d) ::a-known))
            "the losing recheck still forgets the check that failed")))))

(deftest a-pass-check-all-found-before-a-recheck-is-not-written-after-it
  (dotimes [_ 20]
    (reset! on-file #{0 7})
    (let [d (into (rec/draft Filed) {::a 0 ::b 1})
          entered (java.util.concurrent.CountDownLatch. 1)
          release (java.util.concurrent.CountDownLatch. 1)]
      (reset! hold (fn [] (reset! hold nil) (.countDown entered) (.await release 10 java.util.concurrent.TimeUnit/SECONDS)))
      (let [checking (future (rec/check-all [d] ::a-known))]
        (is (.await entered 10 java.util.concurrent.TimeUnit/SECONDS) "the group has its yes from the source")
        (reset! on-file #{})
        (is (= #{::a-known} (set (keys (:failed (rec/recheck d ::a-known))))))
        (.countDown release)
        (is (= [true] (deref checking 10000 nil)))
        (is (= #{::a ::b ::b-not-below-a} (rec/proven-checks d))
            "what the recheck wrote stays, and the group's pass of ::a-known, found before it, is not written")))))

(deftest a-check-all-that-loses-the-race-forgets-only-what-failed
  (dotimes [_ 20]
    (reset! on-file #{})
    (let [d (into (rec/draft Filed) {::a 0 ::b 1})
          entered (java.util.concurrent.CountDownLatch. 1)
          release (java.util.concurrent.CountDownLatch. 1)]
      (reset! hold (fn [] (reset! hold nil) (.countDown entered) (.await release 10 java.util.concurrent.TimeUnit/SECONDS)))
      (let [checking (future (rec/check-all [d] ::a-known))]
        (is (.await entered 10 java.util.concurrent.TimeUnit/SECONDS) "the group has its no from the source")
        (is (true? (rec/check d ::a)) "another run writes the memory meanwhile")
        (.countDown release)
        (is (= #{::a-known} (set (keys (:failed (first (deref checking 10000 nil)))))))
        (is (= #{::a} (rec/proven-checks d))
            "the other run's pass stays; the group's passes, found from an older memory, are not written")))))

(deftest a-check-all-that-loses-the-race-forgets-what-failed-where-the-other-run-passed-it
  (dotimes [_ 20]
    (reset! on-file #{})
    (let [d (into (rec/draft Filed) {::a 0 ::b 1})
          entered (java.util.concurrent.CountDownLatch. 1)
          release (java.util.concurrent.CountDownLatch. 1)]
      (reset! hold (fn [] (reset! hold nil) (.countDown entered) (.await release 10 java.util.concurrent.TimeUnit/SECONDS)))
      (let [checking (future (rec/check-all [d] ::a-known))]
        (is (.await entered 10 java.util.concurrent.TimeUnit/SECONDS) "the group has its no from the source")
        (reset! on-file #{0 7})
        (is (true? (rec/check d ::a-known)) "another run passes it meanwhile")
        (.countDown release)
        (is (= #{::a-known} (set (keys (:failed (first (deref checking 10000 nil)))))))
        (is (= #{::a ::b ::b-not-below-a} (rec/proven-checks d))
            "the group forgets the check it found failing, over the other run's pass")))))

(deftest a-memory-built-by-hand-around-the-type-proves-nothing-its-proof-does-not
  ;; Each memory claims every check passing on bad entries, with a proof that does not show
  ;; it: another sealed value, the bad entries themselves, and a draft of the type that no
  ;; check was marked on.
  (let [t (record/type-of Heist)
        bad (assoc entries ::h/take -1)
        all (clojure.lang.Reflector/getInstanceField (:recognitum.record/hot t) "all")
        unmarked (.newInstance (.getConstructor ^Class (:recognitum.record/draft-class t) (make-array Class 0))
                               (object-array 0))]
    (doseq [[what proof] [["another value" h/italian-job] ["the entries" bad] ["an unmarked draft" unmarked]]]
      (testing what
        (let [forged (Draft. bad (atom (Memo. t bad (:ids t) #{} proof all)) nil)]
          (is (= #{} (rec/proven-checks forged)))
          (is (map? (first (rec/check-all [forged] rec/every))))
          (is (= :recognitum/check-failed (:error (err #(rec/seal forged))))))))))

;;; Many drafts at once: seal-all, drafting-all and drafting.

(def ^:private held-seen
  "What each `Crate`'s `held` check found in its field: `:draft` or `:other`."
  (atom []))

(rec/defproven Crate [held n]
  rec/checks
  (held [] (swap! held-seen conj (if (rec/draft? held) :draft :other)) (some? held))
  (n [] (int? n)))

(defn- heist-draft [] (into (rec/draft Heist) entries))
(defn- crate [held] (-> (rec/draft Crate) (assoc ::held held) (assoc ::n 0)))

(deftest seal-all-walks-every-container
  (let [shape {:map    {:k (heist-draft)}
               :vec    [(heist-draft) 1]
               :list   (list (heist-draft))
               :set    #{(heist-draft)}
               :lazy   (map identity [(heist-draft)])
               :cons   (cons (heist-draft) [2])
               :keys   {(heist-draft) :v}
               :sealed h/italian-job
               :plain  "s"}
        out (rec/seal-all shape)]
    (is (instance? Heist (get-in out [:map :k])))
    (is (vector? (:vec out)))
    (is (instance? Heist (get-in out [:vec 0])))
    (is (= 1 (get-in out [:vec 1])))
    (is (list? (:list out)) "a list stays a list")
    (is (instance? Heist (first (:list out))))
    (is (every? #(instance? Heist %) (:set out)))
    (is (vector? (:lazy out)) "a lazy sequence becomes a vector")
    (is (instance? Heist (first (:lazy out))))
    (is (= [Heist Long] (map class (:cons out))) "so does any other sequence")
    (is (vector? (:cons out)))
    (is (instance? Heist (key (first (:keys out)))) "a draft in key position is sealed")
    (is (identical? h/italian-job (:sealed out)) "a sealed value is the very value given")
    (is (= "s" (:plain out)))))

(deftest seal-all-does-not-enter-a-sealed-value
  (let [inner (heist-draft)
        lazy (map inc (range 3))
        held-draft (rec/seal (crate inner))
        held-lazy (rec/seal (crate lazy))
        [a b] (rec/seal-all [held-draft held-lazy])]
    (is (identical? held-draft a))
    (is (identical? inner (::held a)) "the draft it holds is left a draft")
    (is (identical? held-lazy b))
    (is (not (realized? lazy)) "and a sequence it holds is not realized")))

(deftest seal-all-seals-inner-drafts-first
  (reset! held-seen [])
  (let [[out] (rec/seal-all [(crate (crate (heist-draft)))])]
    (is (instance? Crate out))
    (is (instance? Crate (::held out)))
    (is (instance? Heist (::held (::held out))))
    (is (= [:other :other] @held-seen) "each holder was checked holding the sealed value")))

(deftest seal-all-checks-each-level-in-one-pass
  (reset! house/calls [])
  (rec/seal-all [(heist-draft) {:x [(assoc (heist-draft) ::h/crew #{"Lyle"} ::h/cuts {"Lyle" 3000})]}
                 (crate (heist-draft))])
  (is (= 1 (count @house/calls)) "three drafts of one level read the source once"))

(deftest seal-all-is-all-or-nothing
  (reset! held-seen [])
  (let [bad (assoc (heist-draft) ::h/take -1)
        shape {:a [(heist-draft) (crate bad)] :b (heist-draft)}
        e (err #(rec/seal-all shape))
        path [:a 1 ::held]]
    (is (= :recognitum/drafts-failed (:error e)))
    (is (= #{path} (set (keys (:failures e)))) "only the draft that failed, by its path")
    (is (= (err #(rec/seal (assoc (heist-draft) ::h/take -1))) (get-in e [:failures path]))
        "with what seal throws for it")
    (is (= [:draft] @held-seen) "the holder of a failed draft is checked, holding that draft")
    (testing ":drafts is the shape with every draft in place"
      (let [ds (:drafts e)]
        (is (every? rec/draft? [(get-in ds [:a 0]) (get-in ds [:a 1]) (get-in ds path) (:b ds)]))
        (is (= -1 (get-in ds (conj path ::h/take))))))
    (testing "mended at the failed path, it seals again, running only what is left"
      (reset! house/calls [])
      (let [out (rec/seal-all (assoc-in (:drafts e) (conj path ::h/take) 3000))]
        (is (instance? Heist (get-in out path)))
        (is (instance? Crate (get-in out [:a 1])))
        (is (empty? @house/calls) "the source's answer was remembered")))))

(deftest seal-all-reports-a-refused-draft-without-running-it
  (reset! house/calls [])
  (let [e (err #(rec/seal-all [(assoc (heist-draft) :bogus 1)]))]
    (is (= {:error :recognitum/undeclared-keys :type 'demo.heist/Heist :keys #{:bogus}}
           (select-keys (get-in e [:failures [0]]) [:error :type :keys])))
    (is (empty? @house/calls))))

(deftest a-draft-in-key-position-ends-its-path-with-the-key-step
  (let [bad (assoc (heist-draft) ::h/take -1)
        e (err #(rec/seal-all {:m {bad 1}}))]
    (is (= #{[:m bad :recognitum.core/key]} (set (keys (:failures e)))))))

(deftest drafting-seals-only-what-it-opened
  (testing "a sealed value is opened, changed and sealed"
    (let [v (rec/drafting h/italian-job #(assoc % ::h/name "The Bank Job"))]
      (is (instance? Heist v))
      (is (= "The Bank Job" (::h/name v))))
    (is (= :recognitum/check-failed
           (:error (err #(rec/drafting h/italian-job (fn [d] (assoc d ::h/take -1))))))))
  (testing "a draft is changed and given back unsealed, nothing run"
    (reset! house/calls [])
    (let [d (into (rec/draft Heist) (dissoc entries ::h/name))
          out (rec/drafting d #(assoc % ::h/name "The Bank Job"))]
      (is (rec/draft? out))
      (is (= "The Bank Job" (::h/name out)))
      (is (= #{} (rec/proven-checks out)))
      (is (empty? @house/calls)))))

(defn- renamed
  "A step that renames a heist, sealed or not, as a caller writes it once for both."
  [x]
  (rec/drafting x #(assoc % ::h/name "The Bank Job")))

(deftest a-drafting-step-inside-drafting-all-leaves-the-seal-to-it
  (is (instance? Heist (renamed h/italian-job)))
  (let [inner (heist-draft)
        shape {:job h/italian-job :crate (rec/seal (crate inner))}
        _ (reset! held-seen [])
        out (rec/drafting-all shape (fn [m] (-> m (update :job renamed) (update :crate #(assoc % ::n 1)))))]
    (is (= "The Bank Job" (::h/name (:job out))))
    (is (instance? Heist (:job out)))
    (is (instance? Crate (:crate out)))
    (is (= 1 (::n (:crate out))))
    (is (instance? Heist (::held (:crate out)))
        "the opened crate is a draft, so seal-all enters it and seals the draft it holds")
    (is (= [:other] @held-seen) "then checks the crate again, holding the sealed value")))

(deftest drafting-all-may-return-another-shape
  (let [out (rec/drafting-all [h/italian-job (heist-draft)] (fn [xs] {:first (first xs) :all xs}))]
    (is (every? #(instance? Heist %) (cons (:first out) (:all out))))))

(deftest seal-all-walks-a-map-entry-outside-a-map
  (let [[out] (rec/seal-all [(crate (first {:k (heist-draft)}))])]
    (is (instance? Crate out))
    (is (map-entry? (::held out)))
    (is (instance? Heist (val (::held out))) "the crate is checked after the draft in its entry"))
  (let [bad (assoc (heist-draft) ::h/take -1)]
    (is (= #{[0 1]} (set (keys (:failures (err #(rec/seal-all [(first {:k bad})])))))) "a value's index is 1")
    (is (= #{[0 0]} (set (keys (:failures (err #(rec/seal-all [(first {bad :v})])))))) "a key's is 0")))

(deftest a-collection-the-walk-does-not-enter-holds-no-draft
  ;; A queue is neither a vector nor a sequence: the walk leaves it as it is, so a draft holding
  ;; one is of the lowest level and shares the others' source call.
  (reset! house/calls [])
  (let [q (conj clojure.lang.PersistentQueue/EMPTY 1)
        e (err #(rec/seal-all [(heist-draft) (assoc (heist-draft) ::h/getaway q)]))]
    (is (= #{[1]} (set (keys (:failures e)))))
    (is (identical? q (get-in e [:drafts 1 ::h/getaway])))
    (is (= 1 (count @house/calls)))))

;;; ------------------------------------------------------------------ edge cases

(rec/defproven Tray [item]
  rec/checks
  (item [] (some? item)))

(deftest seal-refuses-what-is-not-a-draft-or-a-value
  (is (= :recognitum/not-a-draft (:error (err #(rec/seal {::item 1})))))
  (is (= :recognitum/not-a-draft (:error (err #(rec/seal {::item 1} rec/every))))))

(def ^:private pair-log (atom []))

(rec/defproven Pair [a b]
  rec/checks
  (a [] (swap! pair-log conj ::a) (int? a))
  (b [] (swap! pair-log conj ::b) (int? b))
  (b-not-below-a [] (swap! pair-log conj ::b-not-below-a) (>= b a)))

(deftest recheck-all-runs-on-a-sealed-value-what-it-selects-only
  (let [v (map->Pair {::a 0 ::b 1})]
    (reset! pair-log [])
    (is (= [true] (rec/recheck-all [v] ::b-not-below-a)))
    (is (= [::b-not-below-a] @pair-log))
    (is (rec/sealed? v))))

(deftest seal-all-seals-a-draft-after-every-draft-it-holds-at-any-depth
  (let [leaf #(assoc (rec/draft Tray) ::item 1)
        outer (assoc (rec/draft Tray) ::item [(leaf) (assoc (rec/draft Tray) ::item (leaf))])
        out (rec/seal-all [outer])]
    (is (rec/sealed? (first out)))
    (is (not-any? rec/draft? (tree-seq coll? seq out)))))

(deftest a-displaced-value-still-prints-through-its-own-to-string
  (let [form '(recognitum.core/defproven Shown [a]
                recognitum.core/checks (a [] (int? a))
                Object (toString [this] (str "Shown " a)))
        _ (binding [*ns* (the-ns 'recognitum.draft-test)] (eval form))
        v (@(ns-resolve 'recognitum.draft-test 'map->Shown) {::a 1})]
    (binding [*ns* (the-ns 'recognitum.draft-test)] (eval form))
    (is (not (rec/sealed? v)))
    (is (= "Shown 1" (.toString ^Object v)))))

;;; ------------------------------------------------------------------ the walk over records, sorted collections and metadata

(defrecord Plain [a b])

(rec/defproven-in Rack [held]
  rec/checks
  (held [] (some? held)))

(defn- tray [item] (assoc (rec/draft Tray) ::item item))
(defn- failing-tray [] (assoc (rec/draft Tray) ::item nil))
(def ^:private by-item (fn [x y] (compare (str (::item x)) (str (::item y)))))

(defn- sealed-tray? [x] (and (rec/sealed? x) (instance? Tray x)))

(deftest seal-all-walks-a-plain-record
  (let [out (rec/seal-all (assoc (->Plain (tray 1) [(tray 2)]) :extra (tray 3)))]
    (is (instance? Plain out) "a record stays a record of its class")
    (is (every? sealed-tray? [(:a out) (get-in out [:b 0]) (:extra out)])))
  (is (= {:m 1} (meta (rec/seal-all (with-meta (->Plain (tray 1) 0) {:m 1})))) "and keeps its metadata")
  (let [e (err #(rec/seal-all (->Plain (failing-tray) [(failing-tray)])))]
    (is (= #{[:a] [:b 0]} (set (keys (:failures e)))))
    (is (instance? Plain (:drafts e)))
    (is (every? rec/draft? [(get-in e [:drafts :a]) (get-in e [:drafts :b 0])]))))

(deftest seal-all-keeps-sorted-collections-and-their-comparators
  (let [out (rec/seal-all {:map    (sorted-map :a (tray 1) :b 2)
                           :map-by (sorted-map-by > 1 (tray 1) 2 (tray 2))
                           :keys   (sorted-map-by by-item (tray 1) :a (tray 2) :b)
                           :set    (sorted-set [1 (tray 1)] [2 (tray 2)])
                           :set-by (sorted-set-by by-item (tray 1) (tray 2))})]
    (is (every? sorted? (vals out)))
    (is (= [2 1] (keys (:map-by out))))
    (is (= (.comparator ^clojure.lang.Sorted (sorted-map-by > 1 2))
           (.comparator ^clojure.lang.Sorted (:map-by out))))
    (is (identical? by-item (.comparator ^clojure.lang.Sorted (:keys out))))
    (is (identical? by-item (.comparator ^clojure.lang.Sorted (:set-by out))))
    (is (every? sealed-tray? (concat (vals (get out :map-by)) (keys (:keys out)) (map second (:set out))
                                     (:set-by out) [(get-in out [:map :a])]))))
  (testing "a failure names its path, and :drafts keeps the collection and its comparator"
    (let [bad (failing-tray)
          e (err #(rec/seal-all {:keys (sorted-map-by by-item bad :a) :set-by (sorted-set-by by-item (tray 1) bad)
                                 :map (sorted-map :a (failing-tray))}))]
      (is (= #{[:keys bad :recognitum.core/key] [:set-by bad] [:map :a]} (set (keys (:failures e)))))
      (is (identical? by-item (.comparator ^clojure.lang.Sorted (get-in e [:drafts :keys]))))
      (is (identical? by-item (.comparator ^clojure.lang.Sorted (get-in e [:drafts :set-by]))))
      (is (every? rec/draft? (get-in e [:drafts :set-by]))))))

(deftest seal-all-keeps-metadata
  (let [m {:m 1}
        shape {:map    (with-meta {:a (tray 1)} m)
               :vec    (with-meta [(tray 1)] m)
               :list   (with-meta (list (tray 1)) m)
               :lazy   (with-meta (map identity [(tray 1)]) m)
               :set    (with-meta #{(tray 1)} m)
               :sorted (with-meta (sorted-map :a (tray 1)) m)
               :record (with-meta (->Plain (tray 1) nil) m)}
        out (rec/seal-all shape)]
    (doseq [[k v] out]
      (is (= m (meta v)) (str k " keeps its metadata")))
    (is (list? (:list out)))
    (is (vector? (:lazy out)) "a sequence becomes a vector holding its metadata")
    (testing "and so does :drafts"
      (let [e (err #(rec/seal-all [(with-meta (list 0 (failing-tray)) m) (with-meta (map identity [(failing-tray)]) m)]))]
        (is (= #{[0 1] [1 0]} (set (keys (:failures e)))))
        (is (= [m m] (map meta (:drafts e))))))))

(deftest seal-all-walks-nests-of-these
  (let [m {:r 1}
        shape (with-meta (->Plain (sorted-map :k (with-meta [(tray 1) #{(tray 2)}] {:v 1}))
                                  (with-meta (list (sorted-set-by by-item (tray 3))) {:l 1}))
                m)
        out (rec/seal-all shape)]
    (is (instance? Plain out))
    (is (= m (meta out)))
    (is (= {:v 1} (meta (get-in out [:a :k]))))
    (is (= {:l 1} (meta (:b out))))
    (is (identical? by-item (.comparator ^clojure.lang.Sorted (first (:b out)))))
    (is (not-any? rec/draft? (tree-seq coll? seq out))))
  (let [e (err #(rec/seal-all (->Plain (sorted-map :k [0 #{(failing-tray)}]) (list (sorted-set-by by-item (failing-tray))))))]
    (is (= 2 (count (:failures e))))
    (is (= #{[:a :k 1] [:b 0]} (set (map #(subvec % 0 (dec (count %))) (keys (:failures e))))))))

(deftest seal-all-enters-a-defproven-in-value-holding-these
  (let [m {:m 1}
        out (rec/seal-all [(map->Rack {::held (with-meta (sorted-map :k (->Plain (tray 1) nil)) m)})])
        held (::held (first out))]
    (is (instance? Rack (first out)))
    (is (sorted? held))
    (is (= m (meta held)))
    (is (instance? Plain (:k held)))
    (is (sealed-tray? (get-in held [:k :a]))))
  (is (= #{[0 ::held :k :a]}
         (set (keys (:failures (err #(rec/seal-all [(map->Rack {::held (sorted-map :k (->Plain (failing-tray) nil))})]))))))))

(deftest drafting-all-opens-sealed-values-in-these-and-keeps-them
  (let [v (rec/seal (tray 1))
        m {:m 1}
        shape {:record (with-meta (->Plain v nil) m)
               :keys   (sorted-map-by by-item v :a)
               :set-by (with-meta (sorted-set-by by-item v) m)
               :list   (with-meta (list v) m)
               :entry  (first {v v})}
        seen (atom nil)
        out (rec/drafting-all shape (fn [s] (reset! seen s) s))]
    (is (every? rec/draft? [(get-in @seen [:record :a]) (key (first (:keys @seen))) (first (:set-by @seen))
                            (first (:list @seen)) (key (:entry @seen)) (val (:entry @seen))]))
    (is (every? sealed-tray? [(get-in out [:record :a]) (key (first (:keys out))) (first (:set-by out))
                              (first (:list out)) (key (:entry out)) (val (:entry out))]))
    (is (instance? Plain (:record out)))
    (is (map-entry? (:entry out)))
    (is (identical? by-item (.comparator ^clojure.lang.Sorted (:keys out))))
    (is (identical? by-item (.comparator ^clojure.lang.Sorted (:set-by out))))
    (is (= [m m m] (map (comp meta out) [:record :set-by :list])))))
