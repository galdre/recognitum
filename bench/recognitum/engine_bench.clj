(ns recognitum.engine-bench
  "`recognitum.engine` against a naive engine that runs the same check bodies as plain fns, in
  wait order, each read calling its source at once with one key. Sources answer at once, so
  the rows measure the engines' own cost; the call counts are what a slow source would see.

    clojure -M:bench -e \"(require 'recognitum.engine-bench)(recognitum.engine-bench/run)\""
  (:require
   [clojure.walk :as walk]
   [recognitum.engine :as e]))

;;; ------------------------------------------------------------- sources and checks

(def calls (atom 0))

(defn- source [f] (fn [ks] (swap! calls inc) (into {} (for [x ks] [x (f x)]))))

(def cars   (source #(when (#{0 1} (mod % 7)) true)))
(def colls  (source (fn [x] {:owner (mod (inc x) 50)})))
(def users  (source (fn [x] {:active? (even? x)})))
(def nxt    (source #(mod (* 2 %) 1000)))
(def vetted (source odd?))

(def checks
  '{:k         {:after #{}           :body (if (int? k) true {:k k})}
    :xs        {:after #{}           :body (if (vector? xs) true {:xs xs})}
    :dependent {:after #{:k}         :body (let [c (fetch recognitum.engine-bench/colls k)]
                                             (if (:active? (fetch recognitum.engine-bench/users (:owner c)))
                                               true
                                               {:inactive (:owner c)}))}
    :each      {:after #{:xs}        :body (let [m (fetch-each recognitum.engine-bench/vetted xs)]
                                             (if (every? true? (map m xs)) true {:unvetted (vec (remove m xs))}))}
    :guarded   {:after #{}           :body (if (or (not (extant? g)) (fetch recognitum.engine-bench/cars g))
                                             true
                                             {:not-on-file g})}
    :chain     {:after #{:dependent} :body (if (fetch recognitum.engine-bench/cars k) true {:no-car k})}
    :loop      {:after #{:k}         :body (loop [x k n 0]
                                             (if (< n 3)
                                               (recur (fetch recognitum.engine-bench/nxt x) (inc n))
                                               (if (even? x) true {:ended x})))}})

(def fields '[k xs g])

;;; ------------------------------------------------------------- the naive engine

(defn- prep [body]
  (walk/prewalk (fn [f]
                  (cond (and (seq? f) (= 'extant? (first f))) (list 'present? (keyword (second f)))
                        (and (symbol? f) (some #{f} fields))    (list 'read-field (keyword f))
                        :else f))
                body))

(defn- naive-define [checks]
  (let [order (loop [done [] seen #{}]
                (if (= (count done) (count checks))
                  done
                  (let [ready (sort (remove seen (filter #(every? seen (:after (checks %))) (keys checks))))]
                    (recur (into done ready) (into seen ready)))))]
    (binding [*ns* (the-ns 'recognitum.engine-bench)]
      (vec (for [id order]
             [id (:after (checks id))
              (eval `(fn [~'read-field ~'present? ~'fetch ~'fetch-each] ~(prep (:body (checks id)))))])))))

(defn- naive-run [engine values]
  (let [fetch (fn [src x] (get (src [x]) x))
        fetch-each (fn [src xs] (into {} (for [x (distinct xs)] [x (fetch src x)])))]
    (mapv (fn [v]
            (let [rf (fn [k] (if (contains? v k) (get v k) (throw (ex-info "absent" {:absent k}))))
                  pr #(contains? v %)]
              (reduce (fn [{:keys [failed blocked] :as acc} [id after f]]
                        (if (some #(or (contains? failed %) (contains? blocked %)) after)
                          (update acc :blocked conj id)
                          (let [r (try (f rf pr fetch fetch-each)
                                       (catch clojure.lang.ExceptionInfo x (ex-data x)))]
                            (if (true? r) acc (assoc-in acc [:failed id] r)))))
                      {:failed {} :blocked #{}}
                      engine)))
          values)))

;;; ------------------------------------------------------------- measuring

(defn- values [n spread]
  (let [r (java.util.Random. 42)]
    (vec (for [_ (range n)]
           (cond-> {:k (.nextInt r spread) :xs (vec (repeatedly (.nextInt r 4) #(.nextInt r spread)))}
             (.nextBoolean r) (assoc :g (.nextInt r spread)))))))

(defn- per-value-us
  "Median microseconds per value of `f` over `vs`, after warming up."
  [f vs]
  (dotimes [_ 20] (f vs))
  (let [ts (sort (for [_ (range 31)]
                   (let [t (System/nanoTime)] (f vs) (- (System/nanoTime) t))))]
    (/ (nth ts 15) 1000.0 (count vs))))

(defn- calls-of [f vs] (reset! calls 0) (f vs) @calls)

(defn- engine-body
  "The engine's check for `body`: field symbols become `&field` reads, and `fetch`,
  `fetch-each` and `extant?` the engine's read forms."
  [body]
  (let [reads '{fetch &fetch, fetch-each &fetch-each}
        body (walk/prewalk (fn [f]
                             (cond (and (seq? f) (= 'extant? (first f))) (list '&extant? (keyword (second f)))
                                   (and (seq? f) (reads (first f)))     (cons (reads (first f)) (rest f))
                                   (and (symbol? f) (some #{f} fields)) (list '&field (keyword f))
                                   :else f))
                           body)]
    (binding [*ns* (the-ns 'recognitum.engine-bench)]
      (eval (e/body-form (walk/macroexpand-all body))))))

(defn run
  "Prints µs per value and source calls per run for each engine and batch."
  []
  (let [eng (e/define (update-vals checks #(update % :body engine-body)))
        lib (fn [vs] (e/run-all (mapv #(vector eng % #{}) vs)))
        naive (let [n (naive-define checks)] (fn [vs] (naive-run n vs)))]
    (assert (= (naive (values 200 1000)) (lib (values 200 1000))))
    (doseq [[label vs] [["1,000 values, keys under 10" (values 1000 10)]
                        ["1,000 values, keys under 1,000" (values 1000 1000)]
                        ["1 value" (values 1 1000)]]]
      (println (format "%-32s naive %7.2f us/value %6d calls | engine %7.2f us/value %4d calls"
                       label (per-value-us naive vs) (calls-of naive vs)
                       (per-value-us lib vs) (calls-of lib vs))))))
