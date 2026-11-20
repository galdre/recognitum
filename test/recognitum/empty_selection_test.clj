(ns recognitum.empty-selection-test
  "A selection that selects nothing in a type: no check of the type, and no required field's
  presence. A seal of a value of a `defproven-in` type by such a selection, other than
  `rec/every`, is refused before any check runs, in `seal` and `seal-all` alike, and `proves?`
  by it is false. Drafts, sealed values, the runs and the probes answer as for any selection.
  `rec/selects-nothing?` asks it."
  (:require
   [clojure.string :as str]
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]
   [recognitum.record]))

(rec/defconcern permission "Whether the actor may do the action.")
(rec/defconcern audit "Checks an auditor reads.")

(rec/defchecks spare "A bundle no type here binds." [x]
  rec/checks
  (spare-int [] (int? x)))

(def ^:private log (atom []))

(defn- ran! [id] (swap! log conj id) nil)

(defn- ran
  "`[answer runs]`: what `(f)` returns, or the ex-data of the ex-info it throws, and a map from
  each check that ran to the number of its runs."
  [f]
  (reset! log [])
  (let [r (try (f) (catch clojure.lang.ExceptionInfo e (ex-data e)))]
    [r (frequencies @log)]))

(defn- err [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))

;; The writer of Grant forgot the flag on `allowed`: meant (allowed [] permission ...).
(rec/defproven-in Grant [actor action]
  rec/checks
  (actor [] (ran! ::actor) (string? actor))
  (allowed [] (ran! ::allowed) (= action :read)))

(rec/defproven-in Order [buyer verb]
  rec/checks
  (buyer [] (ran! ::buyer) (string? buyer))
  (may-order [] permission (ran! ::may-order) (= verb :read)))

(rec/defproven-in Label [text]
  rec/checks
  (text [] (ran! ::text) (string? text)))

(rec/defproven-in OpenLabel [caption]
  rec/checks
  (caption [] (ran! ::caption) (string? caption))
  (anyone-may-read [] permission "Anyone may read a label." (ran! ::anyone-may-read) true))

(rec/defproven-in Crate [label qty]
  rec/checks
  (qty [] (ran! ::qty) (int? qty))
  (may-ship [] permission (ran! ::may-ship) (pos? qty)))

(rec/defproven-in Bare [^:optional e])

(rec/defproven-in Pair [u v]
  rec/checks
  (u [] (ran! ::u) (int? u)))

(rec/defproven Request [who what]
  rec/checks
  (who [] (ran! ::who) (string? who))
  (what-ok [] (ran! ::what-ok) (= what :read)))

(def ^:private selects-nothing-in-grant
  "Each way of selecting nothing in Grant."
  [permission ::permission audit (rec/union) (rec/except rec/every rec/every) (rec/except ::allowed ::allowed)
   spare spare-int (rec/reading ::text)])

(deftest a-seal-by-a-concern-no-check-carries-is-refused-test
  (testing "the forgotten flag: nothing runs, nothing is written, and the error says why"
    (let [g (map->Grant {::actor "a" ::action :write})
          [r runs] (ran #(rec/seal g permission))
          msg (ex-message (err #(rec/seal g permission)))]
      (is (= {:error :recognitum/selects-nothing :type 'recognitum.empty-selection-test/Grant :selection permission} r))
      (is (= {} runs))
      (is (= #{} (rec/proven-checks g)))
      (is (false? (rec/proves? g permission)))
      (is (str/includes? msg (str 'recognitum.empty-selection-test/Grant)))
      (is (str/includes? msg (str ::permission)))
      (is (str/includes? msg "carries"))
      (is (str/includes? msg "flag"))
      (is (str/includes? msg (str "(nothing-to-prove [] " ::permission)))))
  (testing "every way of selecting nothing, whatever the value holds or has passed"
    (doseq [sel selects-nothing-in-grant
            m [{::actor "a" ::action :read} {::actor 1} {}]
            sealed-first? [false true]]
      (let [g (map->Grant m)
            _ (when sealed-first? (try (rec/seal g) (catch clojure.lang.ExceptionInfo _)))
            before (rec/proven-checks g)
            [r runs] (ran #(rec/seal g sel))]
        (is (= :recognitum/selects-nothing (:error r)) (pr-str sel m))
        (is (= {} runs))
        (is (= before (rec/proven-checks g)))
        (is (false? (rec/proves? g sel)) (pr-str sel m))))))

(deftest the-refusal-comes-before-the-floor-test
  (testing "a value that would fail its shape check, or lacks a required field"
    (doseq [m [{::text 5} {}]]
      (let [l (map->Label m)
            [r runs] (ran #(rec/seal l permission))
            [r2 runs2] (ran #(rec/seal-all [l] permission))]
        (is (= {:error :recognitum/selects-nothing :type 'recognitum.empty-selection-test/Label :selection permission} r))
        (is (= {} runs))
        (is (= :recognitum/drafts-failed (:error r2)))
        (is (= {[0] r} (:failures r2)))
        (is (identical? l (first (:drafts r2))))
        (is (= {} runs2))))))

(deftest generic-code-over-several-types-test
  (let [order (map->Order {::buyer "b" ::verb :read})
        label (map->Label {::text "t"})
        open (map->OpenLabel {::caption "c"})]
    (testing "a type with nothing for the concern is refused; one that says so seals"
      (is (identical? order (rec/seal order permission)))
      (is (= :recognitum/selects-nothing (:error (ex-data (err #(rec/seal label permission))))))
      (let [[r runs] (ran #(rec/seal open permission))]
        (is (identical? open r))
        (is (= {::caption 1 ::anyone-may-read 1} runs)))
      (is (rec/proves? order permission))
      (is (rec/proves? open permission))
      (is (false? (rec/proves? label permission))))
    (testing "check-all is unchanged"
      (is (= [true true] (rec/check-all [(map->Order {::buyer "b" ::verb :read}) (map->Label {::text "t"})]
                                        permission))))
    (testing "selects-nothing? tells them apart"
      (is (= [false true false] (mapv #(rec/selects-nothing? permission %) [order label open]))))))

(deftest seal-all-refuses-at-the-path-of-the-value-test
  (let [label (map->Label {::text "t"})
        crate (map->Crate {::label label ::qty 2})
        order (map->Order {::buyer "b" ::verb :read})
        shape {:orders [order] :crates [crate]}
        [r runs] (ran #(rec/seal-all shape permission))]
    (is (= :recognitum/drafts-failed (:error r)))
    (is (= {[:crates 0 ::label] {:error :recognitum/selects-nothing :type 'recognitum.empty-selection-test/Label :selection permission}}
           (:failures r)))
    (is (= {::buyer 1 ::may-order 1 ::qty 1 ::may-ship 1} runs) "every other value ran")
    (is (rec/proves? order permission))
    (is (rec/proves? crate permission))
    (is (false? (rec/proves? label permission)))
    (is (= #{} (rec/proven-checks label)))
    (is (= shape (:drafts r)))
    (testing "without a selection, or by every, the same shape seals"
      (is (= shape (rec/seal-all shape)))
      (is (= shape (rec/seal-all shape rec/every))))))

(deftest every-is-never-refused-test
  (testing "on a type with no check"
    (let [b (map->Bare {})]
      (is (true? (rec/selects-nothing? rec/every b)))
      (is (identical? b (rec/seal b rec/every)))
      (is (identical? b (rec/seal b)))
      (is (rec/proves? b rec/every))
      (is (= [b] (rec/seal-all [b] rec/every)))
      (is (= :recognitum/selects-nothing (:error (ex-data (err #(rec/seal b (rec/union)))))))))
  (testing "a seal by every does not make a value prove a selection that selects nothing"
    (let [g (map->Grant {::actor "a" ::action :read})]
      (is (identical? g (rec/seal g rec/every)))
      (is (rec/proves? g rec/every))
      (is (false? (rec/proves? g permission)))
      (is (= #{} (rec/proven-concerns g))))))

(deftest a-presence-is-something-to-select-test
  (let [p (map->Pair {::u 1})]
    (testing "reading a required field no check reads asks its presence"
      (is (false? (rec/selects-nothing? (rec/reading ::v) p)))
      (is (= #{::v} (:missing (ex-data (err #(rec/seal p (rec/reading ::v))))))))
    (testing "shape less its named checks asks the presence of each required field"
      (is (false? (rec/selects-nothing? (rec/except rec/shape ::u) p)))
      (is (true? (rec/selects-nothing? (rec/except rec/shape rec/shape) p))))))

(deftest the-runs-drafts-sealed-values-and-probes-are-unchanged-test
  (let [g (map->Grant {::actor "a" ::action :write})]
    (testing "check, recheck, check-all and recheck-all run nothing and answer true"
      (is (= [true {}] (ran #(rec/check g permission))))
      (is (= [true {}] (ran #(rec/recheck g permission))))
      (is (= [[true] {}] (ran #(rec/check-all [g] permission))))
      (is (= [[true] {}] (ran #(rec/recheck-all [g] permission)))))
    (testing "the probes"
      (is (= [true {}] (ran #(rec/probe Grant {::actor "a" ::action :write} permission nil))))
      (is (= [[true] {}] (ran #(rec/probe-all Grant [{}] permission nil))))
      (is (true? (rec/probe Request {} permission)))))
  (testing "a draft: proves? asks what it remembers, check answers true, seal-all seals it"
    (let [d (into (rec/draft Request) {::who "w" ::what :write})]
      (is (true? (rec/selects-nothing? permission d)))
      (is (true? (rec/check d rec/shape)))
      (is (true? (rec/proves? d permission)))
      (is (= [true {}] (ran #(rec/check d permission))))
      (is (= :recognitum/draft-selection (:error (ex-data (err #(rec/seal d permission))))))
      (is (= {[0] :recognitum/check-failed}
             (update-vals (:failures (ex-data (err #(rec/seal-all [d] permission)))) :error)))))
  (testing "a sealed value proves every selection and seals as it is"
    (let [s (rec/seal (into (rec/draft Request) {::who "w" ::what :read}))]
      (is (true? (rec/selects-nothing? permission s)))
      (is (identical? s (rec/seal s permission)))
      (is (true? (rec/proves? s permission)))
      (is (= [s] (rec/seal-all [s] permission))))))

(deftest selects-nothing?-answers-for-values-drafts-and-classes-test
  (let [g (map->Grant {})
        d (rec/draft Request)]
    (doseq [x [g Grant d Request]]
      (testing (pr-str x)
        (is (true? (rec/selects-nothing? permission x)))
        (is (true? (rec/selects-nothing? (rec/union) x)))
        (is (false? (rec/selects-nothing? rec/every x)))
        (is (false? (rec/selects-nothing? rec/shape x)))))
    (doseq [x [g Grant]]
      (is (false? (rec/selects-nothing? ::allowed x))))
    (doseq [x [Bare (map->Bare {})]]
      (is (true? (rec/selects-nothing? rec/every x)))
      (is (true? (rec/selects-nothing? rec/shape x))))
    (testing "a check id of another type is refused, as by every op"
      (is (= :recognitum/unknown-name (:error (ex-data (err #(rec/selects-nothing? ::who g)))))))
    (testing "it runs nothing and writes nothing"
      (is (= [true {}] (ran #(rec/selects-nothing? permission g))))
      (is (= #{} (rec/proven-checks g))))))

(def ^:private scratch 'recognitum.empty-selection-test.scratch)

(defn- define-flip
  "Defines `Flip` in a scratch namespace, its one check carrying `permission` where `carries?`.
  Returns its `map->Flip`."
  [carries?]
  (binding [*ns* (create-ns scratch)]
    (refer-clojure)
    (alias 'rec 'recognitum.core)
    (eval (list 'rec/defproven-in 'Flip '[a]
                'rec/checks
                (if carries?
                  '(ok [] :recognitum.empty-selection-test/permission (int? a))
                  '(ok [] (int? a)))))
    @(ns-resolve *ns* 'map->Flip)))

(deftest a-redefinition-leaves-no-stale-answer-test
  (try
    (let [none (define-flip false)
          v1 (none {(keyword (str scratch) "a") 1})]
      (is (true? (rec/selects-nothing? permission v1)))
      (is (= :recognitum/selects-nothing (:error (ex-data (err #(rec/seal v1 permission))))))
      (let [with (define-flip true)
            v2 (with {(keyword (str scratch) "a") 1})]
        (testing "a selection that selected nothing selects a check of the new definition"
          (is (false? (rec/selects-nothing? permission v2)))
          (is (identical? v2 (rec/seal v2 permission)))
          (is (rec/proves? v2 permission)))
        (let [again (define-flip false)
              v3 (again {(keyword (str scratch) "a") 1})]
          (testing "and the reverse"
            (is (true? (rec/selects-nothing? permission v3)))
            (is (= :recognitum/selects-nothing (:error (ex-data (err #(rec/seal v3 permission))))))
            (is (false? (rec/proves? v2 permission)) "a displaced value proves nothing")))))
    (finally (remove-ns scratch))))

(deftest whether-a-selection-selects-nothing-is-worked-out-once-per-type-test
  (testing "after the first seal by a selection, a seal, proves? or seal-all by it looks the answer up"
    (let [calls (atom 0)
          selected @#'recognitum.record/selected
          vs (vec (repeatedly 100 #(map->Grant {::actor "a" ::action :read})))]
      (with-redefs [recognitum.record/selected (fn [t s] (swap! calls inc) (selected t s))]
        (doseq [sel [(rec/union permission audit) (rec/union ::actor ::allowed)]]
          (try (rec/seal (first vs) sel) (catch clojure.lang.ExceptionInfo _))
          (reset! calls 0)
          (doseq [v vs]
            (try (rec/seal v sel) (catch clojure.lang.ExceptionInfo _))
            (rec/proves? v sel))
          (try (rec/seal-all vs sel) (catch clojure.lang.ExceptionInfo _))
          (is (= 0 @calls) (pr-str sel)))))))

(deftest the-refusal-names-the-type-and-the-selection-as-a-caller-writes-it-test
  (let [g (map->Grant {})
        msg #(ex-message (err (fn [] (rec/seal g %))))
        t "recognitum.empty-selection-test/Grant has no check that "
        tail (str ", so a seal by it would prove nothing. If a check of Grant should carry it, give that check its"
                  " flag after its waits. If Grant has nothing to prove for it, give Grant a check that carries it"
                  " and passes")
        selects " selects, and no required field whose presence it asks"]
    (testing "a concern, as its value or its keyword: the remedy shows a passing check that carries it"
      (doseq [sel [permission ::permission]]
        (is (= (str t "carries " ::permission tail ", as in (nothing-to-prove [] " ::permission
                    " \"Why Grant has nothing to prove.\" true)")
               (msg sel)))))
    (testing "any other selection, shown as it is written"
      (doseq [[sel shown] [[(rec/union) "(rec/union)"]
                           [(rec/union permission audit) (str "(rec/union " ::permission " " ::audit ")")]
                           [(rec/except rec/every rec/every) "(rec/except rec/every rec/every)"]
                           [(rec/except rec/shape rec/pure rec/every) "(rec/except rec/shape rec/pure rec/every)"]
                           [(rec/reading ::text) (str "(rec/reading " ::text ")")]
                           [spare "recognitum.empty-selection-test/spare"]
                           [spare-int (str ::spare-int)]]]
        (is (= (str t shown selects tail) (msg sel)) shown)))))
