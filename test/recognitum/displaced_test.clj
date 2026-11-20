(ns recognitum.displaced-test
  "Values and drafts of a displaced definition, one that a later definition of the type
  replaced: `check`, `recheck`, `check-all`, `recheck-all` and `seal` refuse them before any
  check runs, a batch that holds one refuses whole, and each refusal has the keyword and the
  message of a write to that value, or of the seal of that draft."
  (:require
   [clojure.string :as str]
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]))

(def runs
  "The checks that ran, in order: the check bodies of every type here append to it."
  (atom []))

(defn ran!
  "Notes that check `id` ran."
  [id]
  (swap! runs conj id)
  true)

(defn- refusal
  "`[error message]` of the ex-info `(f)` throws, or `[:returned value]`."
  [f]
  (try [:returned (f)]
       (catch clojure.lang.ExceptionInfo e [(:error (ex-data e)) (ex-message e)])))

(defn- error-of [f] (first (refusal f)))

(def ^:private lenient
  '(recognitum.core/defproven Payment [amount ^:optional note]
     recognitum.core/checks
     (amount [] (recognitum.displaced-test/ran! :amount) (int? amount))
     (under-limit [] (recognitum.displaced-test/ran! :under-limit) (< amount 100))))

(def ^:private strict
  '(recognitum.core/defproven Payment [amount ^:optional note]
     recognitum.core/checks
     (amount [] (recognitum.displaced-test/ran! :amount) (pos-int? amount))
     (under-limit [] (recognitum.displaced-test/ran! :under-limit) (< amount 100))))

(def ^:private lenient-in
  '(recognitum.core/defproven-in Ballot [choice]
     recognitum.core/checks
     (choice [] (recognitum.displaced-test/ran! :choice) (string? choice))))

(defn- world
  "`Payment`, defined in a namespace of its own, with a value, a draft and the class of that
  definition held; then defined again, stricter, with a draft of the current definition and a
  sealed value of it. Likewise `Ballot`, a `defproven-in` type, defined twice."
  []
  (let [n (create-ns (gensym "recognitum.displaced-test.w"))
        k (fn [s] (keyword (str n) (name s)))
        ev (fn [form] (binding [*ns* n] (refer-clojure) (eval form)))
        make (fn [t m] (@(ns-resolve n (symbol (str "map->" t))) m))
        _ (ev lenient)
        _ (ev lenient-in)
        old-class (ns-resolve n 'Payment)
        old-value (make 'Payment {(k :amount) -50})
        old-draft (assoc (rec/draft old-class) (k :amount) -50)
        old-full-draft (rec/draft old-value)
        old-ballot (make 'Ballot {(k :choice) "a"})
        _ (rec/seal old-ballot)
        _ (ev strict)
        _ (ev lenient-in)
        current-class (ns-resolve n 'Payment)]
    {:ns n :k k
     :old-value old-value
     :old-draft old-draft
     :old-full-draft old-full-draft
     :class-draft (assoc (rec/draft old-class) (k :amount) -50)
     :old-ballot old-ballot
     :current-draft (assoc (rec/draft current-class) (k :amount) 50)
     :current-value (make 'Payment {(k :amount) 50})
     :current-ballot (make 'Ballot {(k :choice) "b"})}))

(defn- operations
  "Each check operation on `x`, alone and in a batch beside the current values `others`."
  [x others]
  [["check" #(rec/check x rec/every)]
   ["recheck" #(rec/recheck x rec/every)]
   ["check-all" #(rec/check-all [x] rec/every)]
   ["recheck-all" #(rec/recheck-all [x] rec/every)]
   ["check-all, after current values" #(rec/check-all (conj (vec others) x) rec/every)]
   ["check-all, before current values" #(rec/check-all (into [x] others) rec/every)]
   ["recheck-all, after current values" #(rec/recheck-all (conj (vec others) x) rec/every)]
   ["recheck-all, before current values" #(rec/recheck-all (into [x] others) rec/every)]])

(deftest the-check-operations-refuse-a-displaced-value-and-run-nothing
  (let [{:keys [old-value current-draft current-value]} (world)]
    (doseq [[label f] (operations old-value [current-draft current-value])]
      (reset! runs [])
      (let [[e msg] (refusal f)]
        (is (= :recognitum/displaced e) label)
        (is (str/includes? msg "Payment") label)
        (is (str/includes? msg "redefined") label)
        (is (str/includes? msg "(rec/seal (rec/draft v))") label))
      (is (= [] @runs) (str label ": no check of any value ran")))
    (is (= #{} (rec/proven-checks current-draft)) "the current draft beside it remembers nothing new")))

(deftest the-check-operations-refuse-a-displaced-draft-as-its-seal-does
  (let [{:keys [old-draft old-full-draft class-draft current-draft current-value]} (world)]
    (doseq [[which d] [["a draft held across the redefinition" old-draft]
                       ["a draft that remembered every check before it" old-full-draft]
                       ["a draft opened from the class held" class-draft]]
            [label f] (operations d [current-draft current-value])]
      (reset! runs [])
      (is (= (refusal #(rec/seal d)) (refusal f)) (str which ", " label))
      (is (= :recognitum/displaced-constructor (error-of f)) (str which ", " label))
      (is (= [] @runs) (str which ", " label ": no check of any value ran")))
    (is (str/includes? (second (refusal #(rec/check old-draft rec/every))) "map->Payment"))
    (is (= #{} (rec/proven-checks old-draft)) "the displaced draft remembers nothing")
    (is (= #{} (rec/proven-checks current-draft)) "the current draft beside it remembers nothing new")))

(deftest a-batch-of-several-types-refuses-whole-before-any-check
  (let [{:keys [old-value old-draft current-draft current-ballot]} (world)]
    (doseq [x [old-value old-draft]
            xs [[current-ballot current-draft x] [x current-ballot current-draft]]
            f [rec/check-all rec/recheck-all]]
      (reset! runs [])
      (is (some? (error-of #(f xs rec/every))))
      (is (= [] @runs)))
    (is (= #{} (rec/proven-checks current-ballot)))))

(deftest seal-refuses-a-displaced-value-as-a-write-does
  (let [{:keys [k old-value]} (world)
        write (refusal #(assoc old-value (k :amount) 7))]
    (is (= :recognitum/displaced (first write)))
    (reset! runs [])
    (is (= write (refusal #(rec/seal old-value))))
    (is (= write (refusal #(rec/seal old-value rec/every))))
    (is (= write (refusal #(rec/check old-value rec/every))))
    (is (= [] @runs))
    (testing "seal-all reports it with the same keyword"
      (is (= :recognitum/displaced
             (-> (try (rec/seal-all [old-value]) (catch clojure.lang.ExceptionInfo e (ex-data e)))
                 :failures (get [0]) :error))))))

(deftest a-displaced-defproven-in-value-is-refused-alike
  (let [{:keys [old-ballot current-ballot]} (world)]
    (doseq [[label f] (operations old-ballot [current-ballot])]
      (reset! runs [])
      (is (= :recognitum/displaced (error-of f)) label)
      (is (= [] @runs) label))
    (is (= :recognitum/displaced (error-of #(rec/seal old-ballot))))))

(deftest a-displaced-value-or-draft-proves-nothing-and-reads-no-selection
  (let [{:keys [ns k old-value old-full-draft old-draft class-draft old-ballot]} (world)
        current-class (ns-resolve ns 'Payment)]
    (doseq [[label x] [["a displaced value" old-value] ["a displaced draft that remembered every check" old-full-draft]
                       ["a displaced draft" old-draft] ["a draft of the class held" class-draft]
                       ["a displaced defproven-in value" old-ballot] ["the current class" current-class]
                       ["a plain map" {(k :amount) 5}]]
            sel [rec/every rec/shape (k :amount) (rec/union) ::typo :no.such/thing 42 nil "s"]]
      (is (false? (rec/proves? x sel)) (str label ", " (pr-str sel))))))

(deftest drafting-proves-a-displaced-value-under-the-current-definition
  (let [{:keys [k old-value]} (world)
        good (into {} (assoc (into {} old-value) (k :amount) 5))]
    (testing "the value fails the current, stricter check"
      (is (= :recognitum/check-failed (error-of #(rec/drafting old-value identity))))
      (is (= :recognitum/drafts-failed (error-of #(rec/drafting-all [old-value] identity)))))
    (testing "and seals under it once mended"
      (is (rec/sealed? (rec/drafting old-value #(assoc % (k :amount) 5))))
      (is (= [good] (mapv #(into {} %) (rec/drafting-all [old-value] (fn [[d]] [(assoc d (k :amount) 5)]))))))))

;;; ------------------------------------------------------------------ the mistaken sinks

(defn- store! [db x] (swap! db conj (into {} x)) :stored)

(deftest a-sink-that-gates-on-a-check-no-longer-stores-a-displaced-value-or-draft
  (let [{:keys [old-value old-draft class-draft]} (world)
        db (atom [])
        gates {"check" (fn [x] (if (true? (rec/check x rec/every)) (store! db x) :refused))
               "recheck" (fn [x] (if (true? (rec/recheck x rec/every)) (store! db x) :refused))
               "check-all" (fn [x] (if (every? true? (rec/check-all [x] rec/every)) (store! db x) :refused))}]
    (doseq [[label gate] gates, x [old-value old-draft class-draft]]
      (is (#{:recognitum/displaced :recognitum/displaced-constructor} (error-of #(gate x))) label))
    (is (= [] @db))))

(deftest a-sink-that-gates-on-proves?-no-longer-stores-an-undeclared-key
  (let [{:keys [ns k current-value]} (world)
        current-class (ns-resolve ns 'Payment)
        db (atom [])
        sink (fn [x] (if (rec/proves? x rec/every) (store! db x) :refused))
        checked (doto (into (rec/draft current-class) {(k :amount) 50 :admin? true}) (rec/check rec/every))
        decorated (assoc (rec/draft current-value) :admin? true)]
    (is (= :refused (sink checked)))
    (is (= :refused (sink decorated)) "a draft of a sealed value, decorated, with no check called")
    (is (= :stored (sink (rec/clean checked))))
    (is (= [{(k :amount) 50}] @db))))
