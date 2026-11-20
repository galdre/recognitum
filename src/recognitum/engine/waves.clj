(ns recognitum.engine.waves
  "A run of engines over a group of values, in waves: [[run-all]]. Every check that can start
  runs until it finishes or parks at a read whose answer is not yet known; then each source is
  called once with every key parked on it, and the next wave begins. Hidden: the plans an
  engine keeps for its last assumed sets, the slots of a run, the parked reads, and how a wave
  calls its sources."
  (:require
   [recognitum.engine.runtime :as rt]
   [recognitum.engine.step :refer [nothing-failed step]])
  (:import
   [clojure.lang Var]
   [java.util ArrayDeque ArrayList HashMap]
   [recognitum.engine.runtime Failure Park]
   [recognitum.engine.step Engine Failed]))

;;; ------------------------------------------------------------- plans

;; The checks of an engine that one run starts, numbered 0 to k-1 in wait order: `at` holds
;; each one's position in the engine, `fns` its body, `counts` how many of its waits run,
;; `starts` those with none, and `dep-off`/`dep-flat` the checks that run and wait on it, the
;; dependents of check i being `dep-flat` from `(dep-off i)` to `(dep-off (inc i))`.
(deftype Plan [key ^long k ^ints at ^objects fns ^ints counts ^ints starts ^ints dep-off ^ints dep-flat])

(defn- plan
  "The plan of `e` in which the checks at the positions `local` maps to 0 and up run, `k` of
  them; `local` holds -1 for the others."
  [^Engine e key ^ints local k]
  (let [k (int k)
        n (alength local)
        at (int-array k)
        ^objects all-fns (.-fns e)
        fns (object-array k)
        counts (int-array k)
        dep-off (int-array (inc k))
        waits (.-waits e)
        deps (.-dependents e)]
    (dotimes [c n]
      (let [i (aget local c)]
        (when (>= i 0) (aset at i c) (aset fns i (aget all-fns c)))))
    (let [n-deps (loop [i 0, total 0]
                   (if (== i k)
                     total
                     (let [c (aget at i)
                           ^ints ws (nth waits c)
                           ^ints ds (nth deps c)]
                       (aset counts i (int (areduce ws j m 0 (if (>= (aget local (aget ws j)) 0) (inc m) m))))
                       (aset dep-off i (int total))
                       (recur (inc i) (+ total (areduce ds j m 0 (if (>= (aget local (aget ds j)) 0) (inc m) m)))))))
          dep-flat (int-array n-deps)
          n-starts (areduce counts i m 0 (if (zero? (aget counts i)) (inc m) m))
          starts (int-array n-starts)]
      (aset dep-off k (int n-deps))
      (loop [i 0, s 0]
        (when (< i k)
          (let [^ints ds (nth deps (aget at i))]
            (loop [j 0, p (aget dep-off i)]
              (when (< j (alength ds))
                (let [d (aget local (aget ds j))]
                  (if (>= d 0)
                    (do (aset dep-flat p d) (recur (inc j) (inc p)))
                    (recur (inc j) p))))))
          (if (zero? (aget counts i))
            (do (aset starts s i) (recur (inc i) (inc s)))
            (recur (inc i) s))))
      (Plan. key k at fns counts starts dep-off dep-flat))))

(defn- plan-of-set
  "The plan of `e` that runs every check but those in `assumed`, a set: the one kept for this
  set where there is one."
  ^Plan [^Engine e assumed]
  (let [^objects plans (.-plans e)
        found (loop [i 0]
                (when (< i 8)
                  (let [^Plan p (aget plans i)]
                    (if (and p (identical? assumed (.-key p))) p (recur (inc i))))))]
    (if found
      found
      (let [ids (.-ids e)
            n (count ids)
            local (int-array n)
            k (loop [c 0, k 0]
                (if (== c n)
                  k
                  (if (contains? assumed (nth ids c))
                    (do (aset local c -1) (recur (inc c) k))
                    (do (aset local c k) (recur (inc c) (inc k))))))
            p (plan e assumed local k)]
        ;; a race may lose a plan or keep one twice; each plan is whole, its fields final
        (let [^ints cursor (.-cursor e)
              i (bit-and (inc (aget cursor 0)) 7)]
          (aset plans i p)
          (aset cursor 0 i))
        p))))

;;; ------------------------------------------------------------- a run

(def ^:private none (Object.))

(deftype Slot [^Engine engine ^Plan plan value ^objects state ^ints remaining ^objects failures])

(deftype Source [src ^HashMap answers ^ArrayList wave])

(deftype Waiting [^Slot slot ^long c ^Park park ^Source source])

(defn- answer
  "The answer to `p` from `answers`, a Failure when the source failed a key it asked for, or
  `none` while a key is unanswered."
  [^HashMap answers ^Park p]
  (letfn [(fail [a] (Failure. (.-src p) a))]
    (if (.-one? p)
      (let [x (.-ks p)]
        (if (.containsKey answers x)
          (let [a (.get answers x)] (if (instance? Throwable a) (fail a) a))
          none))
      (let [ks (.-ks p)
            n (count ks)]
        (if-not (loop [i 0] (or (== i n) (and (.containsKey answers (nth ks i)) (recur (inc i)))))
          none
          ;; the keys are distinct, so they make a map as they stand
          (let [kvs (object-array (* 2 n))]
            (loop [i 0, failed nil]
              (if (< i n)
                (let [x (nth ks i)
                      a (.get answers x)]
                  (aset kvs (* 2 i) x)
                  (aset kvs (inc (* 2 i)) a)
                  (recur (inc i) (or failed (when (instance? Throwable a) a))))
                (cond failed   (fail failed)
                      (<= n 8) (clojure.lang.PersistentArrayMap. kvs)
                      :else    (clojure.lang.PersistentHashMap/create kvs))))))))))

(def ^:private pending
  "What a source's answers hold for a key from when a wave adds it to the source's call until
  the call answers it."
  (Object.))

(defn- call-wave!
  "Calls each source once with the distinct keys parked on it that it was not yet asked for."
  [^ArrayList waiting]
  (let [called (ArrayList. 2)]
    (dotimes [i (.size waiting)]
      (let [^Waiting w (.get waiting i)
            ^Park p (.-park w)
            ^Source s (.-source w)
            ^HashMap answers (.-answers s)
            ^ArrayList wave (.-wave s)]
        (letfn [(want [x]
                  (when-not (.containsKey answers x)
                    (.put answers x pending)
                    (when (.isEmpty wave) (.add called s))
                    (.add wave x)))]
          (if (.-one? p)
            (want (.-ks p))
            (let [ks (.-ks p)] (dotimes [j (count ks)] (want (nth ks j))))))))
    (dotimes [i (.size called)]
      (let [^Source s (.get called i)
            ^ArrayList wave (.-wave s)
            ^HashMap answers (.-answers s)
            ks (clojure.lang.LazilyPersistentVector/createOwning (.toArray wave))
            _ (.clear wave)
            ans (try ((.-src s) ks)
                     (catch Exception e
                       ;; the throw cleared the flag, and the run goes on as a failed read
                       (when (instance? InterruptedException e) (.interrupt (Thread/currentThread)))
                       e))]
        (dotimes [j (count ks)]
          (let [x (nth ks j)]
            (.put answers x (if (instance? Throwable ans) ans (get ans x)))))))))

(defn- plan-for
  "The plan of `e` for an item's `assumed`, a collection of ids."
  ^Plan [^Engine e assumed]
  (plan-of-set e (if (set? assumed) assumed (set assumed))))

(defn- result-of
  "The result of a run of `slot` that ended."
  [^Slot slot]
  (let [^Plan p (.-plan slot)
        ids (.-ids ^Engine (.-engine slot))
        ^ints at (.-at p)
        ^objects state (.-state slot)
        ^objects failures (.-failures slot)
        k (.-k p)]
    (loop [c 0, failed nil, blocked nil]
      (if (== c k)
        (if (or failed blocked) {:failed (or failed {}) :blocked (or blocked #{})} nothing-failed)
        (let [s (aget state c)]
          (recur (inc c)
                 (if (identical? s :recognitum.engine/failed) (assoc (or failed {}) (nth ids (aget at c)) (aget failures c)) failed)
                 (if (identical? s :recognitum.engine/blocked) (conj (or blocked #{}) (nth ids (aget at c))) blocked)))))))

(defn run-all
  "Runs `items`, a sequence of `[engine value assumed]`, as one group. `value` is a map from key
  to field value; the checks in `assumed`, a set of ids, count as passed and do not run. One
  result per item, in order: `{:failed {id failure} :blocked #{id ...}}`.

  A check fails with what its body returns, unless that is exactly `true`; with
  `{:absent key}` when it reads an absent field; and with `{:fetch-failed source :cause
  exception}` when a read failed. Each of these two is an ordinary exception inside the body,
  which the body may catch. Anything else a body throws propagates out of `run-all`, which
  then returns nothing for any item. Every check sees the dynamic bindings in force where
  `run-all` was called."
  [items]
  (let [items (if (vector? items) items (vec items))
        n-items (count items)
        ^objects slots (object-array n-items)
        live (loop [i 0, live 0]
               (if (== i n-items)
                 live
                 (let [[^Engine e value assumed] (nth items i)
                       ^Plan p (plan-for e assumed)
                       k (.-k p)]
                   (if (zero? k)
                     (recur (inc i) live)
                     (do (aset slots i (Slot. e p value (object-array k) (aclone ^ints (.-counts p)) (object-array k)))
                         (recur (inc i) (inc live)))))))]
    (if (zero? live)
      (vec (repeat n-items nothing-failed))
      (let [home (Var/getThreadBindingFrame)
            caches (HashMap.)
            ;; ready checks, each as its slot followed by its position
            ready (ArrayDeque.)
            parked (ArrayList.)]
        (letfn [(source-of [f]
                  (or (.get caches f) (let [s (Source. f (HashMap.) (ArrayList. 4))] (.put caches f s) s)))
                (resume [^Park p a]
                  (Var/resetThreadBindingFrame (.-frame p))
                  (let [r (step (.-k p) a)]
                    (Var/resetThreadBindingFrame home)
                    r))
                (handle [^Slot slot c r]
                  (loop [r r]
                    (if (instance? Park r)
                      (let [^Park p r
                            f (.-src p)
                            ^Source s (source-of f)
                            a (answer (.-answers s) p)]
                        (if (identical? a none)
                          (.add parked (Waiting. slot c p s))
                          (recur (resume p a))))
                      (finish slot c r))))
                (block [^Slot slot d]
                  (let [^objects state (.-state slot)]
                    (when (nil? (aget state d))
                      (aset state d :recognitum.engine/blocked)
                      (let [^Plan p (.-plan slot)
                            ^ints off (.-dep-off p)
                            ^ints flat (.-dep-flat p)]
                        (loop [j (aget off d)]
                          (when (< j (aget off (inc d)))
                            (block slot (aget flat j))
                            (recur (inc j))))))))
                (finish [^Slot slot c r]
                  (let [c (int c)
                        ^objects state (.-state slot)
                        ^ints remaining (.-remaining slot)
                        ^Plan p (.-plan slot)
                        ^ints off (.-dep-off p)
                        ^ints flat (.-dep-flat p)
                        end (aget off (inc c))]
                    (if (identical? r :recognitum.engine/passed)
                      (do (aset state c :recognitum.engine/passed)
                          (loop [j (aget off c)]
                            (when (< j end)
                              (let [d (aget flat j)
                                    m (dec (aget remaining d))]
                                (aset remaining d (int m))
                                (when (and (zero? m) (nil? (aget state d)))
                                  (.add ready slot) (.add ready d)))
                              (recur (inc j)))))
                      (do (aset state c :recognitum.engine/failed)
                          (aset ^objects (.-failures slot) c (.-data ^Failed r))
                          (loop [j (aget off c)]
                            (when (< j end)
                              (block slot (aget flat j))
                              (recur (inc j))))))))
                (start [^Slot slot c]
                  (let [c (int c)]
                    (aset ^objects (.-state slot) c :recognitum.engine/running)
                    (Var/resetThreadBindingFrame home)
                    (let [r (step (aget ^objects (.-fns ^Plan (.-plan slot)) c) (.-value slot))]
                      (Var/resetThreadBindingFrame home)
                      (handle slot c r))))
                (drain []
                  (loop []
                    (when-let [slot (.poll ready)]
                      (start slot (.poll ready))
                      (recur))))]
          (try
            (dotimes [i n-items]
              (when-let [^Slot slot (aget slots i)]
                (let [^ints starts (.-starts ^Plan (.-plan slot))]
                  (dotimes [j (alength starts)] (.add ready slot) (.add ready (aget starts j))))))
            (drain)
            (while (pos? (.size parked))
              (let [batch (ArrayList. parked)]
                (.clear parked)
                (call-wave! batch)
                (dotimes [i (.size batch)]
                  (let [^Waiting w (.get batch i)
                        p (.-park w)]
                    (handle (.-slot w) (.-c w) (resume p (answer (.-answers ^Source (.-source w)) p)))))
                (drain)))
            (finally (Var/resetThreadBindingFrame home))))
        (let [out (object-array n-items)]
          (dotimes [i n-items]
            (aset out i (if-let [slot (aget slots i)] (result-of slot) nothing-failed)))
          (vec out))))))
