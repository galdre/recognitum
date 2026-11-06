(ns recognitum.record-test
  "Sealed values as maps: closed types, required fields, equality, meta, redefinition, and the
  paths that cannot skip the checks."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]
   [recognitum.proof :as proof]
   [recognitum.proof.key-class :as key-class]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(rec/defproven Pair [a ^:optional b ^:optional c]
  rec/checks
  (a [] (int? a))
  (b [] (int? b))
  (c [] (int? c))
  (b-not-below-a [a b] (rec/when-extant b (>= b a)))
  (c-needs-b [] (or (not (rec/extant? c)) (rec/extant? b))))

(def v (map->Pair {::a 0}))

(deftest a-value-reads-and-compares-as-a-map
  (is (= {::a 0} v))
  (is (= v {::a 0}))
  (is (= (hash {::a 0}) (hash v)))
  (is (= #{::a} (set (keys v))))
  (is (nil? (::b v))))

(deftest writes-are-checked-as-one-write-in-any-order
  (is (instance? Pair (merge v {::c 0 ::b 1})))
  (is (instance? Pair (into v {::c 0 ::b 1})))
  (is (instance? Pair (conj v [::b 1])))
  (is (= :recognitum/check-failed (:error (err #(assoc v ::c 1)))) "c needs b")
  (is (= :recognitum/check-failed (:error (err #(dissoc v ::a)))) "a is required")
  (is (identical? v (assoc v ::a 0)) "a write that changes nothing returns the value")
  (is (identical? v (dissoc v ::z))))

;;; A type with one check that reads a source.

(def ^:private registered (atom #{1 2}))
(def ^:private registry-calls (atom 0))

(defn- registry [ks]
  (swap! registry-calls inc)
  (into {} (for [k ks] [k (contains? @registered k)])))

(rec/defproven Listed [a b]
  rec/checks
  (a [] (int? a))
  (b [] (int? b))
  (a-listed [] (rec/fetch registry a)))

(deftest a-sealed-write-asks-a-source-where-a-check-of-its-key-reads-one
  (let [v (map->Listed {::a 1 ::b 0})]
    (reset! registry-calls 0)
    (is (= {::a 2 ::b 0} (assoc v ::a 2)))
    (is (= 1 @registry-calls) "a check that reads a reads the source")
    (is (= :recognitum/check-failed (:error (err #(assoc v ::a 3)))) "and fails where it answers no")
    (is (= #{::a-listed} (set (keys (:failed (err #(assoc v ::a 3)))))))
    (is (= :recognitum/check-failed (:error (err #(merge v {::a 3 ::b 1})))) "so does a write of two keys")
    (is (instance? Listed (merge v {::a 2 ::b 1})))
    (reset! registry-calls 0)
    (is (instance? Listed (assoc v ::b 5)))
    (is (= :recognitum/check-failed (:error (err #(assoc v ::b :x)))))
    (is (zero? @registry-calls) "no check of b reads a source")))

(deftest a-type-is-closed
  (is (= :recognitum/undeclared-keys (:error (err #(map->Pair {::a 0 ::z 1})))))
  (is (= :recognitum/undeclared-keys (:error (err #(assoc v ::z 1)))))
  (is (= {:error :recognitum/undeclared-keys :keys #{::y ::z}}
         (select-keys (err #(merge v {::z 1 ::y 2})) [:error :keys]))
      "a write of several keys, none of them declared"))

(rec/defproven Unread [a b c]
  rec/checks
  (a [] (int? a)))

(deftest a-required-field-no-check-reads-must-still-be-present
  (is (instance? Unread (map->Unread {::a 1 ::b nil ::c nil})))
  (is (= {:error :recognitum/missing-fields :keys #{::b}}
         (select-keys (err #(map->Unread {::a 1 ::c nil})) [:error :keys])))
  (testing "a draft that lacks one"
    (is (= {:error :recognitum/missing-fields :keys #{::b}}
           (select-keys (err #(rec/seal (into (rec/draft Unread) {::a 1 ::c nil}))) [:error :keys]))))
  (testing "one write that removes two fields, through a transient"
    (let [u (map->Unread {::a 1 ::b nil ::c nil})]
      (is (= {:error :recognitum/missing-fields :keys #{::b ::c}}
             (select-keys (err #(persistent! (-> (transient u) (dissoc! ::b) (dissoc! ::c)))) [:error :keys]))))))

(rec/defproven Loose [^:optional x]
  rec/checks
  (x [] (int? x)))

(deftest a-type-with-no-required-field-seals-a-draft
  (is (instance? Loose (rec/seal (rec/draft Loose))))
  (is (instance? Loose (rec/seal (assoc (rec/draft Loose) ::x 1)))))

(deftest plain-map-copies-any-map-with-its-entries-and-meta
  (let [small (with-meta (sorted-map 3 :c 1 :a 2 :b) {:m 1})
        big (into (sorted-map) (map vector (range 9) (range 9)))]
    (is (= small (proof/plain-map small)))
    (is (= (seq small) (seq (proof/plain-map small))) "in the same order")
    (is (= {:m 1} (meta (proof/plain-map small))))
    (is (= big (proof/plain-map big)))
    (is (= {:a 1} (proof/plain-map (java.util.HashMap. {:a 1}))) "a Java map too")))

(deftest meta-travels-with-the-value
  (let [m (with-meta v {:source :test})]
    (is (instance? Pair m))
    (is (= {:source :test} (meta m)))
    (is (= {:source :test} (meta (assoc m ::b 3))))))

(deftest the-installed-write-needs-a-value-to-start-from
  (let [gate (proof/installed key-class/strategy Pair)]
    (is (thrown? IllegalArgumentException (gate nil {::a 1})))
    (is (thrown? IllegalArgumentException (gate {::a 0 ::b 5} {::a 0 ::b 5 ::c 9})))
    (is (instance? Pair (gate v {::a 0 ::b 1})) "from a value, it is the checked write")))

(deftest redefining-a-type-unproves-its-old-values
  (let [ns' (create-ns 'recognitum.record-test.redefined)
        define #(binding [*ns* ns'] (refer-clojure) (eval '(recognitum.core/defproven R [a] recognitum.core/checks (a [] (int? a)))))
        _ (define)
        old ((ns-resolve ns' 'map->R) {:recognitum.record-test.redefined/a 1})]
    (is (rec/sealed? old))
    (define)
    (is (not (rec/sealed? old)))
    (is (not (rec/proves? old rec/every)))
    (is (rec/sealed? ((ns-resolve ns' 'map->R) {:recognitum.record-test.redefined/a 1})))))

(defn- redefinable
  "A namespace of its own and a fn that evaluates `(defproven R [a] ...)` in it, returning R."
  [ns-sym]
  (let [ns' (create-ns ns-sym)]
    (binding [*ns* ns'] (refer-clojure))
    [ns' #(binding [*ns* ns'] (eval '(recognitum.core/defproven R [a] recognitum.core/checks (a [] (int? a)))))]))

(deftest a-displaced-value-reseals-as-the-current-definition-and-prints
  (let [[ns' define] (redefinable 'recognitum.record-test.displaced)
        k :recognitum.record-test.displaced/a
        old-class (define)
        old (with-meta ((ns-resolve ns' 'map->R) {k 1}) {:from :old})
        new-class (define)]
    (is (not (rec/sealed? old)))
    (is (not (rec/proves? old rec/every)))
    (testing "draft then seal gives a value of the current definition, with the old value's meta"
      (let [d (rec/draft old)]
        (is (= #{} (rec/proven-checks d)) "the current definition's checks have not run on it")
        (let [v' (rec/seal d)]
          (is (instance? new-class v'))
          (is (rec/sealed? v'))
          (is (= {k 1} v'))
          (is (= {:from :old} (meta v'))))))
    (testing "it prints as its tagged literal, and the printer's table keeps no entry for any type's class"
      (is (= "#recognitum.record-test.displaced/R #:recognitum.record-test.displaced{:a 1}" (str old) (pr-str old)))
      (is (nil? (get (methods print-method) old-class)))
      (is (nil? (get (methods print-method) new-class))))
    (testing "the readers name the current definition"
      (is (instance? new-class ((get (rec/data-readers) 'recognitum.record-test.displaced/R) {k 2}))))))

(deftest readers-held-across-a-redefinition-refuse-and-say-to-read-again
  (let [[_ define] (redefinable 'recognitum.record-test.held-readers)
        k :recognitum.record-test.held-readers/a
        tname 'recognitum.record-test.held-readers/R
        _ (define)
        held (get (rec/data-readers) tname)
        _ (define)]
    (is (= [(str tname " was redefined: this constructor is of an earlier definition and makes nothing."
                 " Read again with the current readers: (rec/data-readers)")
            {:error :recognitum/displaced-constructor :type tname}]
           (try (held {k 1}) nil
                (catch clojure.lang.ExceptionInfo e [(ex-message e) (ex-data e)]))))
    (is (rec/sealed? ((get (rec/data-readers) tname) {k 1})) "read again, the readers seal")))

(deftest a-draft-of-a-displaced-class-refuses-to-seal
  (let [[ns' define] (redefinable 'recognitum.record-test.held-class)
        k :recognitum.record-test.held-class/a
        tname 'recognitum.record-test.held-class/R
        old-class (define)
        opened-before (into (rec/draft old-class) {k 1})
        new-class (define)
        refusal (fn [d] (try (rec/seal d) nil
                             (catch clojure.lang.ExceptionInfo e [(ex-message e) (ex-data e)])))
        want [(str tname " was redefined: this draft is of an earlier definition and seals nothing."
                   " Make a value of the current definition with recognitum.record-test.held-class/map->R,"
                   " or seal a draft of the class recognitum.record-test.held-class now names R:"
                   " (rec/seal (into (rec/draft R) m))")
              {:error :recognitum/displaced-constructor :type tname}]]
    (is (= want (refusal (into (rec/draft old-class) {k 1}))) "a draft opened from the held class")
    (is (= want (refusal opened-before)) "a draft opened before the redefinition")
    (is (= want (refusal (into (rec/draft old-class) {k :not-an-int}))) "refused before any check runs")
    (testing "the remedies seal"
      (is (rec/sealed? ((ns-resolve ns' 'map->R) {k 1})))
      (is (instance? new-class (rec/seal (into (rec/draft new-class) {k 1})))))))

(deftest a-value-prints-as-its-tagged-literal
  (is (= "#recognitum.record-test/Pair #:recognitum.record-test{:a 0}" (pr-str v))))

(rec/defproven Wide [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22]
  rec/checks
  (f22 [] (int? f22)))

(deftest the-positional-constructor-takes-more-than-twenty-fields
  (is (instance? Wide (apply ->Wide (range 22))))
  (is (thrown? clojure.lang.ArityException (apply ->Wide (range 21)))))

(deftest naming-a-shape-check-in-a-wait-changes-nothing
  (let [ns' (create-ns 'recognitum.record-test.waits)
        define (fn [waits]
                 (binding [*ns* ns'] (refer-clojure)
                   (eval `(recognitum.core/defproven ~'W [~'a]
                            recognitum.core/checks
                            (~'a [] (~'int? ~'a))
                            (~'positive ~waits (~'pos? ~'a))))))
        failed (fn [W] (try ((ns-resolve ns' 'map->W) {:recognitum.record-test.waits/a "x"}) nil
                            (catch clojure.lang.ExceptionInfo e (ex-data e))))]
    (define [])
    (let [unnamed (failed nil)]
      (define '[a])
      (is (= unnamed (failed nil)))
      (is (= #{:recognitum.record-test.waits/positive} (:blocked unnamed))))))

(defn- refusal [form]
  (try (binding [*ns* (the-ns 'recognitum.record-test)] (eval form))
       nil
       (catch clojure.lang.Compiler$CompilerException e (ex-data (ex-cause e)))))

(deftest shape-checks-that-read-each-other-form-a-cycle
  (let [e (refusal '(recognitum.core/defproven Loop [a b]
                      recognitum.core/checks
                      (a [] (int? b))
                      (b [] (int? a))))]
    (is (= :recognitum/refused (:error e)))
    (is (= (str "the waits form a cycle: :recognitum.record-test/a -> :recognitum.record-test/b"
                " -> :recognitum.record-test/a (a check waits on the shape checks of the fields it reads)")
           (:message e))))
  (testing "a cycle of named waits alone says nothing of reads"
    (is (= "the waits form a cycle: :recognitum.record-test/p -> :recognitum.record-test/q -> :recognitum.record-test/p"
           (:message (refusal '(recognitum.core/defproven Loop2 [a]
                                 recognitum.core/checks
                                 (p [q] true)
                                 (q [p] true))))))))

;;; Types of 64 and of 65 checks: the most a mask of one long holds, and one past it.

(defmacro ^:private def-many
  "A type `nm` with one field `a`, its shape check and `n` checks `c<i>`, each passing where
  `a` is below 1000 + i."
  [nm n]
  `(rec/defproven ~nm [~'a]
     rec/checks
     (~'a [] (int? ~'a))
     ~@(for [i (range n)] `(~(symbol (str "c" i)) [] (< ~'a ~(+ 1000 i))))))

(def-many Many64 63)
(def-many Many65 64)

(deftest a-type-of-64-or-more-checks-seals-checks-and-remembers-as-any-other
  (doseq [[T make n] [[Many64 map->Many64 63] [Many65 map->Many65 64]]]
    (testing (str n " invariants")
      (let [k (keyword "recognitum.record-test" "a")
            c (fn [i] (keyword "recognitum.record-test" (str "c" i)))
            v (make {k 1})]
        (is (rec/sealed? (rec/seal (assoc (rec/draft v) k 2))))
        (let [d (assoc (rec/draft v) k 1030)
              e (err #(rec/seal d))]
          (is (= :recognitum/check-failed (:error e)))
          (is (= (set (map c (range 31))) (set (keys (:failed e)))) "c0 to c30 fail at 1030")
          (is (= (into #{k} (map c (range 31 n))) (rec/proven-checks d))
              "the draft remembers each check that passed, the last one included")
          (let [d3 (assoc d k 3)]
            (is (rec/sealed? (rec/seal d3)))
            (is (= (rec/checks-of rec/every T) (rec/proven-checks d3)) "and remembers every check after the seal")))
        (testing "a failure remembered is run again, and is not taken for another check's pass"
          (let [d (assoc (rec/draft v) k 1009)]
            (is (= :recognitum/check-failed (:error (err #(rec/seal d)))))
            (is (= #{(c 9)} (set (keys (:failed (first (rec/check-all [d] (c 9))))))))
            (is (= :recognitum/check-failed (:error (err #(rec/seal d))))))
          (let [d (assoc (rec/draft v) k "x")]
            (is (= #{k} (set (keys (:failed (err #(rec/seal d)))))))
            (is (= #{k} (set (keys (:failed (err #(rec/seal d)))))) "the shape check fails again")))
        (let [ds [(assoc (rec/draft v) k 5) (assoc (rec/draft v) k 1000)]
              [a b] (rec/check-all ds rec/every)]
          (is (true? a))
          (is (= #{(c 0)} (set (keys (:failed b)))) "c0 alone fails at 1000"))
        (is (true? (rec/check (assoc (rec/draft T) k 7) rec/every)))))))

;; Many64 has a mask of its checks, Many65 has none; Tallied counts the runs of its checks.

(def ^:private many-runs (atom 0))

(rec/defproven Tallied [a]
  rec/checks
  (a [] (swap! many-runs inc) (int? a))
  (small [] (swap! many-runs inc) (< a 100)))

(deftest check-all-over-types-with-and-without-masks-remembers-as-check-does
  (let [k (keyword "recognitum.record-test" "a")
        c (fn [i] (keyword "recognitum.record-test" (str "c" i)))
        v64 (map->Many64 {k 1})
        v65 (map->Many65 {k 1})
        ds [(assoc (rec/draft v65) k 1005) (assoc (rec/draft v64) k 2) (rec/draft v65)
            (assoc (rec/draft v64) k 1000) (assoc (rec/draft v65) k 3) (into (rec/draft Tallied) {::a 7})
            (map->Tallied {::a 1})]]
    (reset! many-runs 0)
    (let [[a b c' d e f g] (rec/check-all ds rec/every)]
      (is (= (set (map c (range 6))) (set (keys (:failed a)))) "c0 to c5 fail at 1005")
      (is (true? b))
      (is (true? c') "a draft of a sealed value runs nothing")
      (is (= #{(c 0)} (set (keys (:failed d)))))
      (is (true? e))
      (is (true? f))
      (is (true? g))
      (is (= 2 @many-runs) "the draft of Tallied runs its two checks, and the value runs none"))
    (is (= (into #{k} (map c (range 6 64))) (rec/proven-checks (ds 0))))
    (is (= (rec/checks-of rec/every Many64) (rec/proven-checks (ds 1))))
    (is (= (rec/checks-of rec/every Many65) (rec/proven-checks (ds 2))))
    (is (= (disj (rec/checks-of rec/every Many64) (c 0)) (rec/proven-checks (ds 3))))
    (is (= (rec/checks-of rec/every Many65) (rec/proven-checks (ds 4))))
    (is (= #{::a ::small} (rec/proven-checks (ds 5))))
    (testing "what each draft remembers is what a check of it alone remembers"
      (let [alone [(assoc (rec/draft v65) k 1005) (assoc (rec/draft v64) k 1000)]]
        (doseq [d alone] (rec/check d rec/every))
        (is (= (rec/proven-checks (alone 0)) (rec/proven-checks (ds 0))))
        (is (= (rec/proven-checks (alone 1)) (rec/proven-checks (ds 3))))))
    (testing "drafts that pass every check run nothing again"
      (reset! many-runs 0)
      (is (= [true true] (rec/check-all [(ds 5) (ds 1)] rec/every)))
      (is (zero? @many-runs)))))

;; Two types whose `known` reads one source, Sourced2 with a mask of its checks and Sourced65
;; without one; the source records the keys of each call.

(def ^:private asked-keys (atom []))

(defn- roster [ks]
  (swap! asked-keys conj (vec ks))
  (into {} (for [k ks] [k true])))

(defmacro ^:private def-sourced
  "A type `nm` with fields `a` and `k`, their shape checks, `n` checks `c<i>` of `a`, and `known`,
  which reads `k` from [[roster]]."
  [nm n]
  `(rec/defproven ~nm [~'a ~'k]
     rec/checks
     (~'a [] (int? ~'a))
     (~'k [] (keyword? ~'k))
     ~@(for [i (range n)] `(~(symbol (str "c" i)) [] (< ~'a ~(+ 1000 i))))
     (~'known [] (true? (rec/fetch roster ~'k)))))

(def-sourced Sourced2 0)
(def-sourced Sourced65 62)

(deftest a-group-of-several-types-runs-its-drafts-in-the-order-of-their-types
  ;; The first draft of Sourced65 has nothing to run; the first of either type that has, a
  ;; Sourced2, comes first.
  (let [v2 (map->Sourced2 {::a 1 ::k :x})
        v65 (map->Sourced65 {::a 1 ::k :x})
        ds [(rec/draft v65) (assoc (rec/draft v2) ::k :m) (assoc (rec/draft v65) ::k :w)]]
    (reset! asked-keys [])
    (is (= [true true true] (rec/check-all ds rec/every)))
    (is (= [[:m :w]] @asked-keys) "one call, its keys in the order of the drafts' types")))

(def ^:private tallies (atom {}))
(defn- tally! [id] (swap! tallies update id (fnil inc 0)) true)

(rec/defproven Fetched [a k]
  rec/checks
  (a [] (tally! ::a) (int? a))
  (k [] (tally! ::k) (keyword? k))
  (known [] (tally! ::known) (true? (rec/fetch roster k))))

(deftest a-write-of-a-key-a-source-check-reads-runs-only-that-key-s-readers
  (let [v (map->Fetched {::a 1 ::k :x})]
    (reset! tallies {})
    (is (= :y (::k (assoc v ::k :y))))
    (is (= {::k 1 ::known 1} @tallies))))

;;; An assoc of one key whose checks read no source.

(def ^:private ran (atom []))
(defn- ran! [k] (swap! ran conj k) true)

(rec/defproven Tracked [a b ^:optional c]
  rec/checks
  (a [] (and (ran! ::a) (int? a)))
  (b [] (and (ran! ::b) (int? b)))
  (c [] (and (ran! ::c) (int? c)))
  (a-below-b [a b] (and (ran! ::a-below-b) (< a b))))

(defn- thrown [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e [(ex-message e) (ex-data e)])))

(deftest an-assoc-of-one-key-runs-the-checks-that-read-it-and-no-other
  (let [t (with-meta (map->Tracked {::a 1 ::b 5}) {:m 1})]
    (reset! ran [])
    (let [t' (assoc t ::a 2)]
      (is (= #{::a ::a-below-b} (set @ran)))
      (is (instance? Tracked t'))
      (is (= {::a 2 ::b 5} t'))
      (is (= {:m 1} (meta t')) "the old value's meta"))
    (reset! ran [])
    (is (instance? Tracked (assoc t ::c 0)))
    (is (= [::c] @ran))))

(deftest an-assoc-of-one-key-refuses-as-the-write-of-the-same-entries
  (let [t (map->Tracked {::a 1 ::b 5})]
    (doseq [[k x] [[::a 9] [::a :x] [::b 0] [::c "c"]]]
      (testing (str k " " x)
        (let [by-assoc (thrown #(assoc t k x))]
          (is (= :recognitum/check-failed (:error (second by-assoc))))
          (is (= by-assoc (thrown #(merge t {k x}))))
          (is (= by-assoc (thrown #(conj t [k x])))))))
    (is (= #{::a-below-b} (set (keys (:failed (second (thrown #(assoc t ::a 9))))))))
    (is (= {:failed #{::a} :blocked #{::a-below-b}}
           (let [e (second (thrown #(assoc t ::a :x)))] {:failed (set (keys (:failed e))) :blocked (:blocked e)})))))

(deftest an-assoc-of-one-key-on-a-displaced-value-refuses
  (let [[ns' define] (redefinable 'recognitum.record-test.displaced-assoc)
        k :recognitum.record-test.displaced-assoc/a
        _ (define)
        old ((ns-resolve ns' 'map->R) {k 1})
        _ (define)
        e (err #(assoc old k 2))]
    (is (= :recognitum/displaced (:error e)))
    (is (identical? old (assoc old k 1)) "an assoc that changes nothing returns the value")))

(deftest the-view-a-one-key-write-checks-reads-as-the-map-it-stands-for
  (let [t (with-meta (map->Tracked {::a 1 ::b 5}) {:m 1})
        w (recognitum.record.With. t ::a 2)
        m {::a 2 ::b 5}]
    (is (= m w))
    (is (= w m))
    (is (.equals ^Object w m))
    (is (.equals ^Object m w))
    (is (= (hash m) (hash w)))
    (is (= (.hashCode ^Object m) (.hashCode ^Object w)))
    (is (= 2 (get w ::a) (w ::a) (::a w) (.get ^java.util.Map w ::a)))
    (is (= 5 (get w ::b)))
    (is (= :nf (get w ::c :nf) (w ::c :nf)))
    (is (nil? (get w ::c)))
    (is (and (contains? w ::a) (contains? w ::b) (not (contains? w ::c))))
    (is (= [::a 2] (find w ::a)))
    (is (= [::b 5] (find w ::b)))
    (is (= 2 (count w) (.size ^java.util.Map w)))
    (is (= (set m) (set (seq w)) (set (iterator-seq (.iterator ^Iterable w)))))
    (is (= 7 (reduce-kv (fn [s _ x] (+ s x)) 0 w)))
    (is (= {:m 1} (meta w) (meta (empty w))))
    (is (= (assoc m ::c 0) (assoc w ::c 0)))
    (is (= {::b 5} (dissoc w ::a)))
    (is (= (assoc m ::c 0) (conj w [::c 0])))
    (is (= (str m) (str w)))
    (is (= (set (keys m)) (set (.keySet ^java.util.Map w))))
    (is (.containsValue ^java.util.Map w 2))
    (is (not (.isEmpty ^java.util.Map w)))))

;;; A change of several keys, or a removal.

(defn- sealed
  "What sealing the map `entries` as a value of `old`'s type answers: the value, or the refusal
  it throws."
  [old entries]
  (try (rec/seal (into (rec/draft (class old)) entries))
       (catch clojure.lang.ExceptionInfo e [(ex-message e) (ex-data e)])))

(defn- written
  "What the type's write, as `installed` answers it, answers of `old` and the whole map
  `entries`: the value it seals, or the refusal it throws."
  [old entries]
  (let [write (proof/gate-of (class old))]
    (try (write old entries) (catch clojure.lang.ExceptionInfo e [(ex-message e) (ex-data e)]))))

(defn- changed
  "What the change `f` answers of `old`: the value, or the refusal it throws."
  [old f]
  (try (f old) (catch clojure.lang.ExceptionInfo e [(ex-message e) (ex-data e)])))

(deftest a-change-of-several-keys-runs-the-checks-that-read-them-and-no-other
  (let [t (with-meta (map->Tracked {::a 1 ::b 5}) {:m 1})]
    (doseq [[label f] [["merge" #(merge % {::b 6 ::c 0})] ["into" #(into % {::b 6 ::c 0})]
                       ["conj of a map" #(conj % {::b 6 ::c 0})]
                       ["a transient" #(persistent! (-> (transient %) (assoc! ::b 6) (assoc! ::c 0)))]]]
      (testing label
        (reset! ran [])
        (let [t' (f t)]
          (is (= #{::b ::c ::a-below-b} (set @ran)) "::a is read by no check of ::b or ::c")
          (is (instance? Tracked t'))
          (is (= {::a 1 ::b 6 ::c 0} t'))
          (is (= {:m 1} (meta t')) "the old value's meta"))))
    (let [t (map->Tracked {::a 1 ::b 5 ::c 0})]
      (reset! ran [])
      (is (= {::a 1 ::b 5} (dissoc t ::c)))
      (is (empty? @ran) "the shape check of an optional field passes where it is absent, without running")
      (reset! ran [])
      (is (= {::a 1 ::b 7} (-> (transient t) (dissoc! ::c) (assoc! ::b 7) persistent!)))
      (is (= #{::b ::a-below-b} (set @ran))))))

(rec/defproven Without [a b ^:optional c]
  rec/checks
  (a [] (int? a))
  (b [] (int? b))
  (c [] (int? c))
  (a-below-b [a b] (< a b))
  (c-listed [] (rec/when-extant c (rec/fetch registry c)))
  (a-small [] (< a 1000)) (a-small-1 [] (< a 1001)) (a-small-2 [] (< a 1002)) (a-small-3 [] (< a 1003))
  (a-small-4 [] (< a 1004)) (a-small-5 [] (< a 1005)) (a-small-6 [] (< a 1006)) (a-small-7 [] (< a 1007))
  (a-small-8 [] (< a 1008)) (a-small-9 [] (< a 1009)) (a-small-10 [] (< a 1010)) (a-small-11 [] (< a 1011))
  (a-small-12 [] (< a 1012)) (a-small-13 [] (< a 1013)) (a-small-14 [] (< a 1014)) (a-small-15 [] (< a 1015))
  (a-small-16 [] (< a 1016)) (a-small-17 [] (< a 1017)) (a-small-18 [] (< a 1018)) (a-small-19 [] (< a 1019))
  (a-small-20 [] (< a 1020)) (a-small-21 [] (< a 1021)) (a-small-22 [] (< a 1022)) (a-small-23 [] (< a 1023))
  (a-small-24 [] (< a 1024)) (a-small-25 [] (< a 1025)) (a-small-26 [] (< a 1026)) (a-small-27 [] (< a 1027))
  (a-small-28 [] (< a 1028)) (a-small-29 [] (< a 1029)) (a-small-30 [] (< a 1030)) (a-small-31 [] (< a 1031))
  (a-small-32 [] (< a 1032)) (a-small-33 [] (< a 1033)) (a-small-34 [] (< a 1034)) (a-small-35 [] (< a 1035))
  (a-small-36 [] (< a 1036)) (a-small-37 [] (< a 1037)) (a-small-38 [] (< a 1038)) (a-small-39 [] (< a 1039))
  (a-small-40 [] (< a 1040)) (a-small-41 [] (< a 1041)) (a-small-42 [] (< a 1042)) (a-small-43 [] (< a 1043))
  (a-small-44 [] (< a 1044)) (a-small-45 [] (< a 1045)) (a-small-46 [] (< a 1046)) (a-small-47 [] (< a 1047))
  (a-small-48 [] (< a 1048)) (a-small-49 [] (< a 1049)) (a-small-50 [] (< a 1050)) (a-small-51 [] (< a 1051))
  (a-small-52 [] (< a 1052)) (a-small-53 [] (< a 1053)) (a-small-54 [] (< a 1054)) (a-small-55 [] (< a 1055))
  (a-small-56 [] (< a 1056)) (a-small-57 [] (< a 1057)) (a-small-58 [] (< a 1058)) (a-small-59 [] (< a 1059)))

(rec/defproven Mixed [a b c]
  rec/checks
  (a [] (int? a))
  (b [] (int? b))
  (a-listed [] (rec/fetch registry a)))

(deftest a-change-refuses-and-seals-as-its-entries-seal
  ;; Without has 65 checks, past what a mask of one long holds, and one that reads a source;
  ;; Pair and Tracked have masks; Listed and Mixed have a check that reads a source; Unread
  ;; and Mixed have required fields no check reads.
  (let [pair (map->Pair {::a 0 ::b 1 ::c 2})
        tracked (map->Tracked {::a 1 ::b 5 ::c 0})
        without (map->Without {::a 1 ::b 5 ::c 1})
        listed (map->Listed {::a 1 ::b 0})
        unread (map->Unread {::a 1 ::b 2 ::c 3})
        mixed (map->Mixed {::a 1 ::b 2 ::c 3})
        changes [#(merge % {::b 6 ::c 0}) #(merge % {::a 9 ::c 1}) #(merge % {::a 1009 ::b 2000})
                 #(merge % {::a :x ::b 0}) #(merge % {::b 7 ::z 1 ::y 2}) #(merge % {::c "c" ::b 9})
                 #(into % {::a 2 ::b 3}) #(conj % {::a -1 ::b -2}) #(dissoc % ::a) #(dissoc % ::b)
                 #(dissoc % ::c) #(dissoc % ::z) #(merge % {::a 3}) #(merge % {::z 1})
                 #(persistent! (-> (transient %) (dissoc! ::a) (assoc! ::b 3)))
                 #(persistent! (-> (transient %) (dissoc! ::b) (assoc! ::c 3)))
                 #(persistent! (-> (transient %) (dissoc! ::c) (assoc! ::a 8)))
                 #(persistent! (-> (transient %) (assoc! ::a 2) (assoc! ::a 1)))
                 #(persistent! (-> (transient %) (dissoc! ::c) (assoc! ::b 4)))
                 #(persistent! (-> (transient %) (dissoc! ::c) (assoc! ::a 2)))
                 #(persistent! (-> (transient %) (dissoc! ::b) (dissoc! ::c)))]]
    (doseq [old [pair tracked without listed unread mixed]
            :let [old (with-meta old {:m 1})]
            [i f] (map-indexed vector changes)]
      (testing (str (class old) " change " i)
        (let [mine (changed old f)
              entries (f (into {} old))
              theirs (if (= entries (into {} old)) old (sealed old entries))]
          (is (= theirs mine))
          (is (= (vector? theirs) (vector? mine)))
          (is (= mine (written old entries)) "the write that installed answers answers alike")
          (when-not (vector? mine)
            (is (rec/sealed? mine))
            (is (= (class old) (class mine)))
            (is (= {:m 1} (meta mine)))))))))

(deftest a-change-of-a-key-a-source-check-reads-asks-the-source
  (let [v (map->Listed {::a 1 ::b 0})]
    (reset! registry-calls 0)
    (is (= {::a 2 ::b 1} (merge v {::a 2 ::b 1})))
    (is (= {::a 2 ::b 0} (into v {::a 2})))
    (is (= 2 @registry-calls))
    (reset! registry-calls 0)
    (is (= {::a 1 ::b 3} (into v {::b 3})))
    (is (zero? @registry-calls) "no check of b reads a source")))

(deftest a-change-on-a-displaced-value-refuses
  (let [[ns' define] (redefinable 'recognitum.record-test.displaced-change)
        k :recognitum.record-test.displaced-change/a
        _ (define)
        old ((ns-resolve ns' 'map->R) {k 1})
        _ (define)]
    (is (= :recognitum/displaced (:error (err #(merge old {k 2})))))
    (is (= :recognitum/displaced (:error (err #(dissoc old k)))))
    (is (identical? old (merge old {k 1})) "a change of nothing returns the value")))

(deftest the-view-a-change-checks-reads-as-the-map-it-stands-for
  (let [t (with-meta (map->Tracked {::a 1 ::b 5 ::c 3}) {:m 1})
        removed (proof/removed key-class/strategy)
        w (recognitum.record.Changed. t {::a 2 ::c removed} removed)
        m {::a 2 ::b 5}]
    (is (= m w))
    (is (= w m))
    (is (.equals ^Object w m))
    (is (.equals ^Object m w))
    (is (= (hash m) (hash w)))
    (is (= (.hashCode ^Object m) (.hashCode ^Object w)))
    (is (= 2 (get w ::a) (w ::a) (::a w) (.get ^java.util.Map w ::a)))
    (is (= 5 (get w ::b)))
    (is (= :nf (get w ::c :nf) (w ::c :nf)))
    (is (nil? (get w ::c)))
    (is (and (contains? w ::a) (contains? w ::b) (not (contains? w ::c))))
    (is (= [::a 2] (find w ::a)))
    (is (nil? (find w ::c)))
    (is (= 2 (count w) (.size ^java.util.Map w)))
    (is (= (set m) (set (seq w)) (set (iterator-seq (.iterator ^Iterable w)))))
    (is (= 7 (reduce-kv (fn [s _ x] (+ s x)) 0 w)))
    (is (= {:m 1} (meta w) (meta (empty w))))
    (is (= (assoc m ::c 0) (assoc w ::c 0)))
    (is (= {::b 5} (dissoc w ::a)))
    (is (= (assoc m ::c 0) (conj w [::c 0])))
    (is (= (str m) (str w)))
    (is (= (set (keys m)) (set (.keySet ^java.util.Map w))))
    (is (.containsValue ^java.util.Map w 2))
    (is (not (.isEmpty ^java.util.Map w)))))

(defmacro ^:private def-wide
  "A type `nm` of fields `k0` to `k<n-1>`, each with its shape check, and `k0-below-k1`."
  [nm n]
  `(rec/defproven ~nm [~@(map #(symbol (str "k" %)) (range n))]
     rec/checks
     ~@(for [i (range n)] `(~(symbol (str "k" i)) [] (int? ~(symbol (str "k" i)))))
     (~'k0-below-k1 [] (< ~'k0 ~'k1))))

(def-wide Wide65 65)

(deftest a-change-of-a-type-of-more-than-64-keys-refuses-and-seals-as-its-entries-seal
  (let [k (fn [i] (keyword "recognitum.record-test" (str "k" i)))
        old (map->Wide65 (into {} (for [i (range 65)] [(k i) i])))]
    (doseq [[i f] (map-indexed vector
                               [#(merge % {(k 0) 5 (k 64) 1}) #(merge % {(k 1) -1 (k 64) 1})
                                #(merge % {(k 2) :x (k 3) 1}) #(merge % {(k 0) 5 (k 64) 1})
                                #(into % {(k 1) 9 (k 2) 9}) #(dissoc % (k 5))
                                #(persistent! (-> (transient %) (dissoc! (k 7)) (assoc! (k 8) 1)))])]
      (testing (str "change " i)
        (let [mine (changed old f)
              theirs (sealed old (f (into {} old)))]
          (is (= theirs mine))
          (when-not (vector? mine) (is (rec/sealed? mine))))))))

(def-wide Wide64 64)

(deftest a-change-of-several-keys-runs-the-checks-of-each-key-it-names
  ;; Each change of several keys finds its runner by the keys it names: no two sets of keys
  ;; share one, so a value a check of any key would refuse is refused after every other set
  ;; has been run.
  (doseq [[n make] [[64 map->Wide64] [65 map->Wide65]]]
    (testing (str n " keys")
      (let [k (fn [i] (keyword "recognitum.record-test" (str "k" i)))
            old (make (into {} (for [i (range n)] [(k i) i])))
            others (remove #{2 3} (range n))]
        (is (rec/sealed? (merge old {(k 2) 102 (k 3) 103})))
        (doseq [j others]
          (is (rec/sealed? (merge old {(k 2) 102 (k j) (if (zero? j) -5 (+ 1000 j))})))
          (is (rec/sealed? (merge old {(k 2) 102 (k 3) 103 (k j) (if (zero? j) -5 (+ 1000 j))}))))
        (doseq [j others]
          (is (= :recognitum/check-failed (:error (err #(merge old {(k 2) 102 (k j) :x})))) (str "k" j))
          (is (= :recognitum/check-failed (:error (err #(merge old {(k 2) 102 (k 3) 103 (k j) :x})))) (str "k" j)))))))
