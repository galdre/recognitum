(ns recognitum.engine.runner
  "Runners. A runner is a function that runs some checks of an engine on one value at a time,
  on the calling thread, and answers what a run in waves of that value answers. It is for
  checks whose bodies read no source.

  - [[runner]] makes a runner.
  - [[one-run]] is the run of one check alone, which `recognitum.engine/body-form` compiles
    into each check. The functions that its expansion calls are public for that reason.

  Hidden: which of three cases a runner takes (no check, one check, several)."
  (:require
   [recognitum.engine.runtime :as rt]
   [recognitum.engine.step :refer [failure-of nothing-failed step]])
  (:import
   [clojure.lang Var]
   [recognitum.engine.runtime Park]
   [recognitum.engine.step Engine Failed]))

;;; ------------------------------------------------------------- a runner

(defn- reads-source
  "The ex-info that a runner throws where check `id` reaches a read of a source."
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
  "The `Failed` for `e`, an exception that a body let escape, where `e` is a signal: the
  exception that a read of an absent field or a failed read of a source throws. Rethrows any
  other exception."
  [^Exception e]
  (if-let [d (failure-of e)] (Failed. d) (throw e)))

(defn answer-one
  "A runner's answer for check `id`, whose body ended in `r` and not in `true`. Where `r` is a
  Park, restores `home`, the binding frame from before the body ran, unless it is nil, and
  throws the ex-info of [[reads-source]]."
  [id r home]
  (cond
    (instance? Park r)   (do (when home (Var/resetThreadBindingFrame home))
                             (throw (reads-source id)))
    (instance? Failed r) {:failed {id (.-data ^Failed r)} :blocked #{}}
    :else                {:failed {id r} :blocked #{}}))

(defmacro one-run
  "The run of `check`, whose id is `id`, alone on `value`: what a runner of that one check
  answers. `reads?` is false only where the check's body holds no read of a source; such a
  body cannot park, so the expansion does not restore the binding frame."
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
  what `(first (run-all [[engine value assumed']]))` answers, where `assumed'` is `assumed` plus
  every check that `ids` does not name: a check outside `ids` counts as passed and does not
  run.

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
      ;; one check that waits on no named check: the run that body-form compiled into it,
      ;; where it has one
      (and (== n 1) (zero? (alength ^ints (aget waits 0))))
      (let [id (aget ids 0)
            f (aget fns 0)]
        (if-let [make-run (:recognitum.engine/make-run (meta f))]
          (make-run f id)
          (fn [value assumed] (one-run f id value assumed true))))
      :else
      (fn [value assumed]
        (let [assumed (if (or (nil? assumed) (set? assumed)) assumed (set assumed))
              assumed? (and (some? assumed) (pos? (count assumed)))
              ;; (aget bad i): check i failed or was blocked
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
                          (identical? r :recognitum.engine/passed) (recur (inc i) failed blocked)
                          (instance? Park r)      (do (Var/resetThreadBindingFrame home)
                                                      (throw (reads-source id)))
                          :else                   (do (aset bad i true)
                                                      (recur (inc i) (assoc (or failed {}) id (.-data ^Failed r))
                                                             blocked)))))))))))))))
