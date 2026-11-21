(ns recognitum.engine
  "Check bodies that read sources inline, run in waves over a group of values.

  A check body is ordinary Clojure, its macros expanded. It reads the field whose key is `k`
  with `(&field k)`, asks whether that field is present with `(&extant? k)`, reads a source
  with `(&fetch source key)`, and reads many keys of one source with
  `(&fetch-each source keys)`.

  - [[body-form]] gives the form of the check that a body compiles to.
  - [[define]] makes an engine from a type's checks and the checks that each waits on.
  - [[recognitum.engine.waves/run-all]] runs engines over a group of values.
  - [[recognitum.engine.runner/runner]] makes a function that runs some checks of an engine,
    those that read no source, on one value at a time.

  A run proceeds in waves. Every check that can start runs until it finishes or reaches a read
  whose answer is not yet known. There it parks: it stops, and the run keeps the read. Then
  each source is called once with the keys that the parked checks asked of it, the parked
  checks resume, and the next wave begins. Batching changes how sources are called, never
  what a check answers: every check answers what it would answer if each read called its
  source immediately, with its one key. Within one run:

  - a source is asked for a key at most once, so each call passes distinct keys;
  - a source is asked for a key iff a check that runs reaches a read of that key;
  - a source is called no more times than the longest chain of reads has links. A chain
    follows a path of waits, and each `&fetch` or `&fetch-each` on the path is one link.

  A source is a function of a vector of distinct keys that returns a map from key to answer.
  A key left out of the map reads as nil; an answer that is a Throwable fails the reads of
  that key. A source that throws an Exception fails the reads of every key it was given; an
  Error propagates. The run does not bound how many keys one call passes: a source that needs
  smaller calls splits the keys itself. Sources are compared with `=`, so reads of one source
  share its calls across checks, values and engines."
  (:require
   [recognitum.engine.rewrite :as rewrite]
   [recognitum.engine.runner :refer [one-run]]
   [recognitum.engine.runtime :as rt])
  (:import
   [recognitum.engine.step Engine]))

;;; ------------------------------------------------------------- compiling a body

(defn- with-fields
  "`form` with each `(&field k)` replaced by a read of field `k` of the checked value, and each
  `(&extant? k)` by a test of whether the value holds `k`. The walk tracks no bindings: outside
  a quoted form, a list headed by `&field` or `&extant?` is always a read."
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
  "The form of the check that runs `body`, for a macro to place in its expansion. The form
  evaluates to a function of the checked value. `body` must hold to these:

  - every macro in it is expanded;
  - its reads are `(&field k)`, `(&extant? k)`, `(&fetch src k)` and `(&fetch-each src ks)`,
    each in call position;
  - no `&fetch` or `&fetch-each` stands inside a fn that the body builds, or inside `locking`."
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

(defn- order
  "The ids of `checks`, each after every check it waits on. Throws ex-info whose :error is
  :recognitum.checks/cycle where the waits form a cycle."
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
  "An engine for `checks`, a map `{id {:after #{id ...} :body check}}`:

  - `:after` holds the ids of the checks that this check waits on. A check runs only once
    every check in its `:after` has passed. A check that waits on a check that failed or was
    blocked is blocked: it does not run.
  - `:body` is a function of a value, such as the function that a form from [[body-form]]
    evaluates to.

  Throws ex-info whose :error is :recognitum.checks/unknown-check where a check waits on an id
  that `checks` lacks, and :recognitum.checks/cycle where the waits form a cycle."
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
