(ns recognitum.engine-test
  "The check engine: compiling bodies, definitions, and how a run calls sources, orders checks
  and reports failures. A body here is written with its macros unexpanded and expanded by
  `clojure.walk/macroexpand-all`, as the record layer expands them before the engine sees it,
  and reads a field as the record layer writes the read, `(&field k)`."
  (:require
   [clojure.test :refer [deftest is]]
   [clojure.walk :as walk]
   [recognitum.engine :as e]))

(def ^:dynamic *dyn* :outer)

(def calls "The keys of each source call, in order, since the last reset." (atom []))

(defn inc-src [ks] (swap! calls conj ks) (zipmap ks (map inc ks)))
(defn same-src [ks] (swap! calls conj ks) (zipmap ks ks))
(defn next-src [ks] (swap! calls conj ks) (zipmap ks (map #(mod (* 2 %) 5) ks)))
(defn boom-src [_] (throw (ex-info "down" {})))
(defn odd-fails-src [ks] (zipmap ks (map #(if (odd? %) (ex-info "odd" {}) %) ks)))

(defn- check
  "The check `body` compiles to."
  [body]
  (binding [*ns* (the-ns 'recognitum.engine-test)]
    (eval (e/body-form (walk/macroexpand-all body)))))

(defn- engine [checks]
  (e/define (update-vals checks (fn [c] (update c :body #(if (fn? %) % (check %)))))))

(defn- run1
  "The result of running the checks `checks` over `values`, each with nothing assumed."
  [checks values]
  (let [eng (engine checks)]
    (e/run-all (map (fn [v] [eng v #{}]) values))))

;;; ------------------------------------------------------------- reads and names

(deftest the-read-forms-read
  (reset! calls [])
  (is (= [{:failed {:a [2 {1 2}] :b :absent-g} :blocked #{}}]
         (run1 {:a {:after #{} :body '[(&fetch inc-src (&field :k)) (&fetch-each inc-src [(&field :k)])]}
                :b {:after #{} :body '(if (&extant? :g) false :absent-g)}}
               [{:k 1}])))
  (is (= [[1]] @calls) "one call per run, the key asked once"))

(deftest a-local-named-like-a-read-is-a-local
  (is (= [{:failed {:a [1 2]} :blocked #{}}]
         (run1 {:a {:after #{} :body '(let [fetch (fn [a b] [a b])] (fetch 1 2))}} [{}]))))

(deftest a-var-named-like-a-read-is-that-var
  (let [helper (create-ns 'recognitum.engine-test.helper)]
    (binding [*ns* helper] (refer-clojure) (intern helper 'fetch (fn [m k] (get m k))))
    (let [eng (e/define {:a {:after #{} :body (binding [*ns* helper] (eval (e/body-form '(fetch {:x 1} :x))))}})]
      (is (= [{:failed {:a 1} :blocked #{}}] (e/run-all [[eng {} #{}]]))))))

(deftest a-field-read-is-its-read-form-and-nothing-else
  (is (= [{:failed {:a [1 [2 3] 5 '(&field :k) {:recognitum.checks/absent :g}]} :blocked #{}}]
         (run1 {:a {:after #{} :body '[(&field :k) (let [k 2] [k (inc k)]) ((fn [k] k) 5) '(&field :k)
                                       (try (&field :g) (catch clojure.lang.ExceptionInfo e (ex-data e)))]}}
               [{:k 1}])))
  (is (= [{:failed {:a {:absent :g}} :blocked #{}}]
         (run1 {:a {:after #{} :body '(&field :g)}} [{:k 1}]))))

;;; ------------------------------------------------------------- definitions

(deftest define-refuses-cycles-and-unknown-waits
  (let [err (fn [checks] (try (e/define checks) nil (catch clojure.lang.ExceptionInfo x (:error (ex-data x)))))]
    (is (= :recognitum.checks/cycle (err {:a {:after #{:b} :body true} :b {:after #{:a} :body true}})))
    (is (= :recognitum.checks/cycle (err {:a {:after #{:a} :body true}})))
    (is (= :recognitum.checks/unknown-check (err {:a {:after #{:nope} :body true}})))
    (is (nil? (err {:a {:after #{} :body (constantly true)} :b {:after #{:a} :body (check true)}})))))

;;; ------------------------------------------------------------- runs

(deftest a-run-batches-each-wave-across-checks-and-values
  (reset! calls [])
  (run1 {:one {:after #{} :body '(&fetch next-src (&field :k))}
         :two {:after #{} :body '(&fetch next-src (&fetch next-src (&field :k)))}}
        [{:k 1} {:k 3} {:k 1}])
  (is (= [[1 3] [2]] @calls) "two waves; 1 -> 2 and 3 -> 1, so the second wave asks only for 2"))

(deftest fetch-each-takes-any-collection-of-keys
  (doseq [ks [#{1 2} '(1 2 1) [1 2] (sorted-set 1 2)]]
    (is (= [{:failed {} :blocked #{}}]
           (run1 {:each {:after #{} :body '(= {1 2, 2 3} (&fetch-each inc-src (&field :ks)))}} [{:ks ks}]))
        (pr-str ks))))

(deftest a-check-runs-after-its-waits-pass
  (reset! calls [])
  (let [eng (engine {:a {:after #{} :body '(int? (&field :k))}
                     :b {:after #{:a} :body '(= 1 (&fetch same-src (&field :k)))}
                     :c {:after #{:b} :body true}})]
    (is (= [{:failed {:a false} :blocked #{:b :c}}
            {:failed {:b false} :blocked #{:c}}
            {:failed {} :blocked #{}}
            {:failed {} :blocked #{}}]
           (e/run-all [[eng {:k "x"} #{}] [eng {:k 2} #{}] [eng {:k 1} #{}] [eng {:k "x"} #{:a :b}]])))
    (is (= [[2 1]] @calls) "the blocked and assumed checks read nothing")))

(deftest failures-carry-what-the-body-met
  (let [[r] (run1 {:returned {:after #{} :body '{:k (&field :k)}}
                   :absent   {:after #{} :body '(&field :g)}
                   :failed   {:after #{} :body '(&fetch boom-src (&field :k))}
                   :odd      {:after #{} :body '(&fetch-each odd-fails-src [2 (&field :k)])}
                   :even     {:after #{} :body '(= {2 2} (&fetch-each odd-fails-src [2 2]))}
                   :caught   {:after #{} :body '(try (&fetch boom-src (&field :k))
                                                     (catch clojure.lang.ExceptionInfo _ true))}}
                  [{:k 1}])
        f (:failed r)]
    (is (= {:k 1} (:returned f)))
    (is (= {:absent :g} (:absent f)))
    (is (= boom-src (get-in f [:failed :fetch-failed])))
    (is (= "down" (ex-message (get-in f [:failed :cause]))))
    (is (= "odd" (ex-message (get-in f [:odd :cause]))) "an answer that is a Throwable fails its key")
    (is (= #{:returned :absent :failed :odd} (set (keys f))))))

(deftest an-error-propagates
  (is (thrown? AssertionError (run1 {:a {:after #{} :body '(assert false)}} [{}]))))

(deftest any-other-exception-propagates
  (is (thrown? ArithmeticException (run1 {:a {:after #{} :body '(/ 1 0)}} [{}])))
  (is (thrown? ArithmeticException
               (run1 {:a {:after #{} :body '(/ 1 (&fetch same-src 0))}} [{}]))
      "after a park")
  (is (thrown? ArithmeticException
               (run1 {:a {:after #{} :body '(try (&fetch boom-src 1) (catch clojure.lang.ExceptionInfo _ (/ 1 0)))}}
                     [{}]))
      "from a catch of a failed read"))

(deftest checks-see-the-callers-bindings
  (let [eng (engine {:a {:after #{} :body '(do (&fetch same-src 1) (= :caller *dyn*))}
                     :b {:after #{:a} :body '(= :caller *dyn*)}
                     :c {:after #{} :body '(binding [*dyn* :inner] [(&fetch same-src 1) *dyn*])}})]
    (is (= [{:failed {:c [1 :inner]} :blocked #{}}]
           (binding [*dyn* :caller] (e/run-all [[eng {} #{}]]))))
    (is (= :outer *dyn*))))

(deftest an-empty-group-runs-nothing
  (is (= [] (e/run-all []))))

;;; ------------------------------------------------------------- runners

(deftest a-runner-answers-as-run-all-with-the-others-assumed
  (reset! calls [])
  (let [eng (engine {:a {:after #{} :body '(int? (&field :k))}
                     :b {:after #{:a} :body '(pos? (&field :k))}
                     :c {:after #{:b} :body '(< (&field :k) 10)}
                     :d {:after #{:c} :body '{:d (&field :k)}}
                     :f {:after #{} :body '(= 1 (&fetch same-src (&field :k)))}})
        r (e/runner eng [:a :b :c :d])]
    (doseq [[v assumed] (concat (for [v [{:k "x"} {:k -1} {:k 20} {:k 1} {}]] [v #{}])
                                (for [v [{:k -1} {:k 20} {:k 1}], a [#{:a} #{:b :c}]] [v a]))]
      (is (= (first (e/run-all [[eng v (conj assumed :f)]])) (r v assumed)) [v assumed]))
    (is (= {:failed {:a false} :blocked #{:b :c :d}} (r {:k "x"} #{}))
        "a blocked check blocks the checks that wait on it")
    (is (= {:failed {} :blocked #{}} ((e/runner eng [:b :c]) {:k 5} #{})) "a check outside the runner counts as passed")
    (is (= {:failed {} :blocked #{}} ((e/runner eng []) {:k "x"} #{})))
    (is (= [] @calls) "no source was called but by the runs that held :f")))

(deftest a-runner-of-one-check-or-none-answers-as-run-all-with-the-others-assumed
  (let [eng (engine {:a {:after #{} :body '(int? (&field :k))}
                     :b {:after #{:a} :body '(= 1 (&field :k))}
                     :d {:after #{} :body '{:d (&field :k)}}
                     :f {:after #{} :body '(= 1 (&fetch same-src (&field :k)))}})]
    (doseq [named [[:a] [:b] [:d] []]
            v [{:k "x"} {:k -1} {:k 1} {}]
            assumed [nil #{} [] #{:a} [:b] #{:d :f} (set named) (vec named)]]
      (is (= (first (e/run-all [[eng v (into (set assumed) (remove (set named)) [:a :b :d :f])]]))
             ((e/runner eng named) v assumed))
          [named v assumed]))
    (is (= {:failed {:b false} :blocked #{}} ((e/runner eng [:b]) {:k -1} nil))
        "a check that waits on one outside the runner runs as if that one passed")
    (is (= {:failed {:d {:d 3}} :blocked #{}} ((e/runner eng [:d]) {:k 3} #{})))))

(deftest a-runner-of-one-check-compiled-elsewhere-answers-as-run-all
  ;; A body-form check brings its own run of that check alone; a function of a value does not,
  ;; and the runner runs it itself.
  (is (fn? (::e/make-run (meta (check '(int? (&field :k)))))))
  (let [eng (engine {:a {:after #{} :body (fn [v] (if (int? (:k v)) true {:not-int (:k v)}))}
                     :s {:after #{} :body (fn [_] (throw (ex-info "absent" {:recognitum.checks/absent :k})))}
                     :t {:after #{} :body (fn [_] (throw (ArithmeticException.)))}})]
    (doseq [named [[:a] [:s]], v [{:k 1} {:k "x"} {}], assumed [nil #{} #{:a} [:s]]]
      (is (= (first (e/run-all [[eng v (into (set assumed) (remove (set named)) [:a :s :t])]]))
             ((e/runner eng named) v assumed))
          [named v assumed]))
    (is (thrown? ArithmeticException ((e/runner eng [:t]) {} nil)))))

(deftest a-runner-refuses-a-read-of-a-source
  (reset! calls [])
  (let [eng (engine {:a {:after #{} :body '(int? (&field :k))}
                     :f {:after #{:a} :body '(try (&fetch same-src (&field :k)) (catch Throwable _ true))}
                     :e {:after #{} :body '(= {} (&fetch-each same-src []))}})
        refusal (fn [r v] (try (r v #{}) nil (catch clojure.lang.ExceptionInfo x (ex-data x))))]
    (is (= {:error :recognitum.checks/reads-source :reads-source :f} (refusal (e/runner eng [:a :f]) {:k 1}))
        "whatever the body does with the read")
    (is (= :e (:reads-source (refusal (e/runner eng [:e]) {}))) "a read of no keys")
    (is (= {:failed {:a false} :blocked #{:f}} ((e/runner eng [:a :f]) {:k "x"} #{})) "a blocked check reads nothing")
    (is (= [] @calls))
    (let [eng (engine {:b {:after #{} :body '(binding [*dyn* :inner] (&fetch same-src 1))}})]
      (binding [*dyn* :caller]
        (is (= :b (:reads-source (refusal (e/runner eng [:b]) {}))))
        (is (= :caller *dyn*) "the caller's bindings are restored")))))

(deftest a-runner-propagates-a-throw
  (let [eng (engine {:a {:after #{} :body '(= 1 (/ 1 (&field :k)))}
                     :b {:after #{} :body '(= :caller *dyn*)}})
        r (e/runner eng [:a :b])]
    (is (thrown? ArithmeticException (r {:k 0} #{})))
    (is (thrown? ArithmeticException ((e/runner eng [:a]) {:k 0} #{})) "a runner of one check too")
    (is (true? (binding [*dyn* :caller] (empty? (:failed ((e/runner eng [:b]) {} nil))))))
    (is (= {:failed {} :blocked #{}} (binding [*dyn* :caller] (r {:k 1} #{}))) "and sees the caller's bindings")))
