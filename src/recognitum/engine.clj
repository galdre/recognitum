(ns recognitum.engine
  "Check bodies that read sources inline, run in waves over a group of values.

  A check body is ordinary Clojure, its macros expanded. It reads the field whose key is `k`
  with `(&field k)`, asks whether that field is present with `(&extant? k)`, reads a source
  with `(&fetch source key)`, and many keys of one source with `(&fetch-each source keys)`. [[body-form]] gives the form of
  the check a body compiles to; [[define]] makes an engine from a type's checks and the checks
  each waits on; [[run-all]] runs engines over a group of values; [[runner]] makes a function
  that runs some of an engine's checks, those that read no source, on one value at a time.

  A run proceeds in waves. Every check that can start runs until it finishes or reaches a read
  whose answer is not yet known, where it parks. Then each source is called once with every
  key parked on it, the parked checks resume, and the next wave begins. Batching changes how
  sources are called, never what a check answers: every check answers what it answers when
  each read calls its source at once with one key. Within one run:

  - a source is asked for a key at most once, so each call passes distinct keys;
  - a source is asked for exactly the keys the checks that run reach;
  - a source is called no more times than the longest chain of reads along any path of waits,
    each `&fetch` or `&fetch-each` one link.

  A source is a function of a vector of distinct keys that returns a map from key to answer.
  A key left out of the map reads as nil; an answer that is a Throwable fails the reads of
  that key. A source that throws an Exception fails the reads of every key it was given; an
  Error propagates. A source that needs smaller calls splits the keys it is given. Sources
  are compared with `=`, so reads of one source share its calls across checks, values and
  engines."
  (:require
   [recognitum.engine.rewrite :as rewrite]
   [recognitum.engine.runtime :as rt])
  (:import
   [clojure.lang Var]
   [java.util ArrayDeque ArrayList HashMap]
   [recognitum.engine.runtime Failure Park]))

;;; ------------------------------------------------------------- compiling a body

(defn- with-fields
  "`form` with each `(&field k)` a read of field `k` of the checked value and each
  `(&extant? k)` a test of it. Outside a quoted form, those heads are read forms and nothing
  else, so this knows no scope."
  [form]
  (cond
    (seq? form)
    (let [[h k] form]
      (cond (= 'quote h)    form
            (= '&field h)   (with-meta (list `rt/field rt/value-sym k) (meta form))
            (= '&extant? h) (list `contains? rt/value-sym k)
            :else           (let [out (apply list (map with-fields form))]
                              (if (meta form) (with-meta out (meta form)) out))))
    (map-entry? form) (mapv with-fields form)
    (coll? form)      (into (empty form) (map with-fields) form)
    :else             form))

(defn body-form
  "The form of the check that runs `body`, for a macro to place in its expansion. `body` has
  every macro expanded; its reads are `(&field k)`, `(&extant? k)`, `(&fetch src k)` and
  `(&fetch-each src ks)`, each in call position, the last two outside any fn the body builds
  and outside `locking`."
  [body]
  (let [check (gensym "check") id (gensym "id") value (gensym "value") assumed (gensym "assumed")
        body (with-fields body)]
    ;; The run of this check alone is compiled here too, and held in the check's metadata, so
    ;; that a runner of this one check calls it from code of its own and not from code every
    ;; check shares.
    (with-meta `(fn* [~rt/value-sym] ~(rewrite/rewrite body))
      {::make-run `(fn* [~check ~id]
                     (fn* [~value ~assumed]
                       (one-run ~check ~id ~value ~assumed ~(rewrite/reads? body))))})))

;;; ------------------------------------------------------------- engines

;; `plans` keeps the plans of the last eight assumed sets, the newest at `(aget cursor 0)`
(deftype Engine [ids fns waits dependents ^objects plans ^ints cursor])

(defn- order
  "The ids of `checks`, each after every check it waits on. Throws :recognitum.checks/cycle."
  [checks]
  (loop [done [], seen #{}]
    (if (= (count done) (count checks))
      done
      (let [ready (sort-by str (remove seen (filter #(every? seen (:after (checks %))) (keys checks))))]
        (when (empty? ready)
          (let [left (set (remove seen (keys checks)))]
            (throw (ex-info (str "checks wait on one another in a cycle: " left)
                            {:error :recognitum.checks/cycle :checks left}))))
        (recur (into done ready) (into seen ready))))))

(defn define
  "An engine for `checks`, a map `{id {:after #{id ...} :body check}}`. A check runs only once
  every check in its `:after` has passed; one whose wait failed or was blocked is blocked. A
  `:body` is a function of a value, such as the check a [[body-form]] evaluates to.

  Throws ex-info whose :error is :recognitum.checks/unknown-check when a check waits on an id
  `checks` lacks, and :recognitum.checks/cycle when waits form a cycle."
  [checks]
  (doseq [[id {:keys [after]}] checks, w after :when (not (contains? checks w))]
    (throw (ex-info (str "check " id " waits on " w ", which is not a check")
                    {:error :recognitum.checks/unknown-check :check id :wait w})))
  (let [ids (order checks)
        index (zipmap ids (range))
        waits (mapv (fn [id] (int-array (map index (:after (checks id))))) ids)
        deps (mapv (fn [i] (int-array (keep-indexed (fn [j ^ints ws] (when (some #{i} ws) j)) waits)))
                   (range (count ids)))
        fns (object-array (map (comp :body checks) ids))]
    (Engine. ids fns waits deps (object-array 8) (int-array 1))))

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

(defn- failure-of
  "The failure data of a signal `e` a body let escape, or nil when `e` is no signal."
  [^Exception e]
  (let [d (ex-data e)]
    (cond (contains? d :recognitum.checks/absent)       {:absent (:recognitum.checks/absent d)}
          (contains? d :recognitum.checks/fetch-failed) {:fetch-failed (:recognitum.checks/fetch-failed d)
                                                         :cause (.getCause e)}
          :else                                         nil)))

(deftype Failed [data])

(defn- step
  "Runs `(f x)`, a body or a continuation, to its next Park, or to `::passed` or a Failed.
  Rethrows what the body throws, unless it is a signal."
  [f x]
  (try (let [r (rt/settle (f x))]
         (cond (instance? Park r) r
               (true? r)          ::passed
               :else              (Failed. r)))
       (catch Exception e
         (if-let [d (failure-of e)] (Failed. d) (throw e)))))

(def ^:private nothing-failed {:failed {} :blocked #{}})

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
            ans (try ((.-src s) ks) (catch Exception e e))]
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
                 (if (identical? s ::failed) (assoc (or failed {}) (nth ids (aget at c)) (aget failures c)) failed)
                 (if (identical? s ::blocked) (conj (or blocked #{}) (nth ids (aget at c))) blocked)))))))

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
                      (aset state d ::blocked)
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
                    (if (identical? r ::passed)
                      (do (aset state c ::passed)
                          (loop [j (aget off c)]
                            (when (< j end)
                              (let [d (aget flat j)
                                    m (dec (aget remaining d))]
                                (aset remaining d (int m))
                                (when (and (zero? m) (nil? (aget state d)))
                                  (.add ready slot) (.add ready d)))
                              (recur (inc j)))))
                      (do (aset state c ::failed)
                          (aset ^objects (.-failures slot) c (.-data ^Failed r))
                          (loop [j (aget off c)]
                            (when (< j end)
                              (block slot (aget flat j))
                              (recur (inc j))))))))
                (start [^Slot slot c]
                  (let [c (int c)]
                    (aset ^objects (.-state slot) c ::running)
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

;;; ------------------------------------------------------------- a runner

(defn- reads-source
  "The refusal of a runner's call in which check `id` reached a read of a source."
  [id]
  (ex-info (str "check " id " reads a source, and a runner calls none")
           {:error :recognitum.checks/reads-source :reads-source id}))

(defn assumed?
  "Whether `assumed`, a collection of ids, holds `id`."
  [assumed id]
  (contains? (if (set? assumed) assumed (set assumed)) id))

(def passed
  "A runner's answer where nothing failed."
  nothing-failed)

(defn caught
  "A runner's failure for a signal `e` that a body let escape. Rethrows anything else."
  [^Exception e]
  (if-let [d (failure-of e)] (Failed. d) (throw e)))

(defn answer-one
  "A runner's answer for check `id`, whose body ended in `r` and not in `true`. `home` is the
  binding frame from before the body ran."
  [id r home]
  (cond
    (instance? Park r)   (do (when home (Var/resetThreadBindingFrame home))
                             (throw (reads-source id)))
    (instance? Failed r) {:failed {id (.-data ^Failed r)} :blocked #{}}
    :else                {:failed {id r} :blocked #{}}))

(defmacro one-run
  "The run of `check`, whose id is `id`, alone on `value`, as a runner of it answers. Where
  `reads?` is false, the check's body holds no read of a source, so it cannot park and
  nothing restores the binding frame."
  [check id value assumed reads?]
  `(if (and (some? ~assumed) (assumed? ~assumed ~id))
     passed
     ~(if reads?
        `(let [home# (Var/getThreadBindingFrame)
               r# (try (rt/settle (~check ~value)) (catch Exception e# (caught e#)))]
           (if (true? r#) passed (answer-one ~id r# home#)))
        `(let [r# (try (~check ~value) (catch Exception e# (caught e#)))]
           (if (true? r#) passed (answer-one ~id r# nil))))))

(defn runner
  "A function of a value and a set of assumed ids that runs the checks of `engine` that `ids`
  names, for checks whose bodies read no source. `((runner engine ids) value assumed)` answers
  what `(first (run-all [[engine value assumed']]))` answers, `assumed'` being `assumed` with
  every check `ids` does not name: a check outside `ids` counts as passed and does not run.

  The checks run one after another on the calling thread, in wait order, each to its end. A
  call calls no source: a check that reaches `&fetch` or `&fetch-each` stops at that read,
  and the call throws ex-info whose :error is :recognitum.checks/reads-source and whose
  :reads-source is that check's id. Anything else a body throws propagates, as from
  `run-all`."
  [^Engine engine ids]
  (let [named (set ids)
        all (.-ids engine)
        at (vec (keep-indexed (fn [c id] (when (contains? named id) c)) all))
        local (zipmap at (range))
        n (count at)
        ^objects ids (object-array (map all at))
        ^objects fns (object-array (map #(aget ^objects (.-fns engine) %) at))
        ^objects waits (object-array (map #(int-array (keep local (nth (.-waits engine) %))) at))]
    (cond
      (zero? n)
      (fn [_ _] nothing-failed)
      ;; one check that waits on none named: no array and no loop, and the run its body
      ;; compiled where it has one
      (and (== n 1) (zero? (alength ^ints (aget waits 0))))
      (let [id (aget ids 0)
            f (aget fns 0)]
        (if-let [make-run (::make-run (meta f))]
          (make-run f id)
          (fn [value assumed] (one-run f id value assumed true))))
      :else
      (fn [value assumed]
        (let [assumed (if (or (nil? assumed) (set? assumed)) assumed (set assumed))
              assumed? (and (some? assumed) (pos? (count assumed)))
              ;; true where the check failed or was blocked
              bad (boolean-array n)
              home (Var/getThreadBindingFrame)]
          (loop [i 0, failed nil, blocked nil]
            (if (== i n)
              (if (or failed blocked)
                {:failed (or failed {}) :blocked (or blocked #{})}
                nothing-failed)
              (let [id (aget ids i)]
                (if (and assumed? (contains? assumed id))
                  (recur (inc i) failed blocked)
                  (let [^ints ws (aget waits i)
                        held (loop [j 0]
                               (cond (== j (alength ws))        false
                                     (aget bad (aget ws j))     true
                                     :else                      (recur (inc j))))]
                    (if held
                      (do (aset bad i true)
                          (recur (inc i) failed (conj (or blocked #{}) id)))
                      (let [r (step (aget fns i) value)]
                        (cond
                          (identical? r ::passed) (recur (inc i) failed blocked)
                          (instance? Park r)      (do (Var/resetThreadBindingFrame home)
                                                      (throw (reads-source id)))
                          :else                   (do (aset bad i true)
                                                      (recur (inc i) (assoc (or failed {}) id (.-data ^Failed r))
                                                             blocked)))))))))))))))
