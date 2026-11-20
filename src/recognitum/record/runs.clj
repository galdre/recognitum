(ns recognitum.record.runs
  "A run of a type's checks over one value or a batch of values: [[check]] and [[recheck]] run
  what a selection names in one value, [[check-all]] and [[recheck-all]] in many, and
  [[run-batch]] runs a plan per type over many values in one run of the engine, so that values
  that read the same source share its calls. A draft, or a value of an unsealed type, remembers
  what passed and forgets what failed. [[run-jobs]] runs the jobs of a type's write in one call
  of the engine. Hidden: the table per type of a batch, the partition into drafts and sealed
  values, and the masks."
  (:require
   [clojure.set :as set]
   [recognitum.record.draft :refer [draft? marks-of]]
   [recognitum.record.memory :refer [mask-of passes-mask]]
   [recognitum.record.probe :refer [run-all-plain]]
   [recognitum.record.reports :refer [answer engine-passed]]
   [recognitum.record.selection :refer [absent-of asked]]
   [recognitum.record.types :refer [gate value-type!]]
   [recognitum.record.values :refer [data-of passes-of refuse-displaced! unsealed?]]
   [recognitum.select :as select])
  (:import
   [recognitum.record.draft Draft]))

;;; ------------------------------------------------------------------ running checks

(defn run
  "The result of running every check of `type` on `data` except those in `assumed`."
  [type data assumed]
  ((:recognitum.record/run type) data assumed))

(defn minus
  "`s` less the elements of `known`. Walks `s` through its iterator, and builds no set where
  `known` holds every element."
  [s known]
  (if (identical? s known)
    #{}
    (let [it (.iterator ^Iterable s)]
      (loop [acc #{}]
        (if (.hasNext it)
          (let [x (.next it)]
            (recur (if (contains? known x) acc (conj acc x))))
          acc)))))

(defn run-jobs
  "Runs the `:job` of every entry of `entries` in one call of `run-all`, hands each entry's
  result to its `:done`, and returns `[i result to-run]` for each entry, its `:i` and its
  `:to-run`."
  [run-all entries]
  (if (empty? entries)
    []
    (let [entries (vec entries)
          results (vec (run-all-plain run-all (mapv :job entries)))]
      (loop [j 0, out (transient [])]
        (if (== j (count entries))
          (persistent! out)
          (let [e (entries j)
                r (results j)]
            ((:done e) r)
            (recur (inc j) (conj! out [(:i e) r (:to-run e)]))))))))

(defn- absent-in
  "The required fields that a run of `sel` reports `x` lacks: where `x` is a draft or a value of
  an unsealed type, those whose presence `sel` asks that its entries lack; else nil."
  [type x sel]
  (when (or (draft? x) (unsealed? type))
    (absent-of (asked type sel) (data-of x))))

(defn check
  "Runs the checks `sel` names in `x`, and those they wait on, that `x` does not pass already.
  A draft remembers what passed and forgets what failed. Returns true, or a report
  `{:failed {id {:data :doc :blocked}} :blocked #{id}}` with `:pulled-back` where an `except`
  removed a check that a wait then ran. The report holds under `:missing` the required fields
  that `x`, a draft or a value of an unsealed type, lacks and whose presence `sel` asks
  ([[asked]]), and is a report even where every check passed. Refuses a draft or a value of a
  displaced definition, once `sel` is read, as [[seal]] refuses it, before any check runs."
  [x sel]
  (let [type (value-type! x)
        picked (select/select type sel)]
    (refuse-displaced! type x)
    (if (or (draft? x) (unsealed? type))
      (let [known (passes-of type x)
            to-run (set/difference (select/closure type picked) known)]
        (answer type ((gate type) :recognitum.record/check x picked) sel picked to-run (absent-in type x sel)))
      true)))

(defn recheck
  "Runs the checks `sel` names in `x` whether or not `x` passes them, and those they wait on that
  `x` does not pass. A draft remembers as [[check]] does; a sealed value is left as it is.
  Returns and refuses as [[check]] does."
  [x sel]
  (let [type (value-type! x)
        picked (select/select type sel)
        _ (refuse-displaced! type x)
        known (passes-of type x)
        to-run (into picked (set/difference (select/closure type picked) known))]
    (answer type
            (if (or (draft? x) (unsealed? type))
              ((gate type) :recognitum.record/recheck x picked)
              (run type x (set/difference (:ids type) to-run)))
            sel picked to-run (absent-in type x sel))))

(defn run-batch
  "Runs, over every value in `xs`, what `plan` says for its type in one run of the engine, so
  values that read the same source, of one type or several, share its calls. `(plan type)` is
  `[sel kind]`: the selection, and the kind of run, nil for [[check]]'s, `:recheck` for
  [[recheck]]'s, or `:seal` for a seal's, which adds the floor of each value and reports every
  required field it lacks. Drafts and values of unsealed types remember as the single op would.
  Returns a vector with one answer per value, each true or a report as [[check]] returns.
  Refuses the whole of `xs` before anything runs where it holds a draft or a value of a
  displaced definition, as [[check]] refuses that one."
  [xs plan]
  (let [xs (vec xs)
        n (count xs)
        ;; each type, to what its selection picks in it, the closure of that, its mask, the
        ;; selection, the kind of run, and the fields whose presence the run reports, or nil
        ;; where it reports none: the same for every value of the type in one call
        per-type (java.util.IdentityHashMap.)
        types (mapv (fn [x]
                      (let [type (value-type! x)]
                        (when-not (.containsKey per-type type)
                          (let [[sel kind] (plan type)
                                picked (select/select type sel)
                                closed (select/closure type picked)]
                            ;; a batch that holds a draft or a value of a displaced definition
                            ;; is refused whole, before anything runs
                            (refuse-displaced! type x)
                            (.put per-type type [picked closed (mask-of (:recognitum.record/hot type) closed) sel kind
                                                 ;; a seal names every required field absent,
                                                 ;; whatever its selection asks
                                                 (not-empty (if (= :seal kind) (:recognitum.record/required-v type) (asked type sel)))])))
                        type))
                    xs)
        ;; the drafts, and values of unsealed types, of each type, by index; each runs in its
        ;; type's gate, which reads its memory and runs what it finds
        drafts (java.util.IdentityHashMap.)
        order (java.util.ArrayList.)
        ;; each sealed value that has anything to run, run here
        others (loop [i 0, others (transient [])]
                 (if (== i n)
                   (persistent! others)
                   (let [x (xs i)
                         type (types i)
                         pt (.get per-type type)]
                     (if (or (draft? x) (unsealed? type))
                       ;; through the mask, where the type has one, a draft that passes every
                       ;; check in the closure has nothing to run for check
                       (if (let [m (nth pt 2)]
                             (and m (nil? (nth pt 4)) (draft? x)
                                  (zero? (bit-and-not (long m) (passes-mask type (.-data ^Draft x) (marks-of x))))))
                         (recur (inc i) others)
                         (let [^java.util.ArrayList is (or (.get drafts type)
                                                           (let [is (java.util.ArrayList.)]
                                                             (.put drafts type is)
                                                             (.add order type)
                                                             is))]
                           (.add is i)
                           (recur (inc i) others)))
                       (let [known (passes-of type x)
                             to-run (if (= :recheck (nth pt 4))
                                      (into (nth pt 0) (minus (nth pt 1) known))
                                      (minus (nth pt 1) known))]
                         (recur (inc i)
                                (if (seq to-run)
                                  (conj! others {:i i :to-run to-run
                                                 :job [(:engine type) x (set/difference (:ids type) to-run)]
                                                 :done (fn [_])})
                                  others)))))))
        groups (mapv (fn [type] (let [[picked _ _ _ kind] (.get per-type type)]
                                  [picked xs (vec (.get drafts type)) kind]))
                     order)
        ran (cond
              (seq groups) ((gate (first order)) :recognitum.record/check-all groups others)
              (seq others) (run-jobs (:run-all (types (:i (first others)))) others)
              :else [])
        out (object-array n)
        ;; the required fields a value lacks, where its run reports them
        absent (fn [i] (let [type (types i)
                             x (xs i)]
                         (when-let [ask (nth (.get per-type type) 5)]
                           (when (or (draft? x) (unsealed? type))
                             (absent-of ask (data-of x))))))]
    (doseq [[i r to-run] ran]
      (let [type (types i)
            pt (.get per-type type)]
        ;; a seal's failure is what seal throws, which explains no check an except removed
        (aset out i (answer type r (when-not (= :seal (nth pt 4)) (nth pt 3)) (nth pt 0) to-run (absent i)))))
    ;; a value that ran nothing answers true, unless the run reports the required fields it
    ;; lacks; the fields asked are looked up once for each run of values of one type
    (loop [i 0, acc (transient []), last-type nil, ask nil]
      (if (== i n)
        (persistent! acc)
        (let [a (aget out i)
              type (types i)
              ask (if (identical? type last-type) ask (nth (.get per-type type) 5))]
          (recur (inc i)
                 (conj! acc (if (or (some? a) (nil? ask))
                              (if (some? a) a true)
                              (let [x (xs i)
                                    m (when (or (draft? x) (unsealed? type)) (absent-of ask (data-of x)))]
                                (if m (assoc engine-passed :missing m) true))))
                 type ask))))))

(defn check-all
  "Runs, over every value in `xs`, the checks `sel` names in it and those they wait on that it
  does not pass already, in one run of the engine, so values that read the same source, of one
  type or several, share its calls. Each draft, and each value of an unsealed type, remembers
  what passed and forgets what failed, as under [[check]]. Returns a vector with one answer
  per value, each true or a report as [[check]] returns."
  [xs sel]
  (let [p [sel nil]]
    (run-batch xs (fn [_] p))))

(defn recheck-all
  "Runs, over every value in `xs`, what [[recheck]] would run on it, in one run of the engine.
  Each draft, and each value of an unsealed type, remembers as under [[recheck]]; a sealed
  value is left as it is. Returns as [[check-all]] does."
  [xs sel]
  (let [p [sel :recheck]]
    (run-batch xs (fn [_] p))))
