(ns recognitum.record.walk
  "Many values at once: [[seal-all]] seals each draft it reaches in a nested shape, or none;
  [[drafting-all]] and [[drafting]] open sealed values as drafts, call a function, and seal
  what it answers."
  (:require
   [clojure.string :as str]
   [recognitum.record.draft :refer [draft?]]
   [recognitum.record.reports :refer [all-declared? check-failed displaced-refusal displaced-unsealed
                                      member-of]]
   [recognitum.record.runs :refer [run-batch]]
   [recognitum.record.selection :refer [nothing? selects-nothing-refusal]]
   [recognitum.record.types :refer [current? refuse-type! type-of]]
   [recognitum.record.values :refer [draft orphan? seal unsealed? with-meta-of]]
   [recognitum.select :as select])
  (:import
   [recognitum.record.draft Draft]))

(defn- value?
  "Whether `x` is a value of a type, of any definition, sealed or not: the walk does not enter
  a sealed one. Not a proof: [[sealed?]] and [[proves?]] answer that."
  [x]
  (instance? recognitum.proof.Proven x))

(defn- unsealed-value?
  "Whether `x` is a value of an unsealed type, as its class says: the walk of [[seal-all]]
  enters it as it enters a draft."
  [x]
  (instance? recognitum.proof.Built x))

(defn- displaced-value?
  "Whether `x`, a value of a type, is of a definition that a later one displaced."
  [x]
  (let [t (type-of x)]
    (and (some? t) (not (current? t)))))

;; What [[scan!]] answers of a part of a shape: -1 where it holds no draft and no value the walk
;; enters; else its height, shifted left one bit, with the low bit set where a draft is reached in
;; it. A draft's or an entered value's height is one more than the highest it holds, or 0.

(defn- reach
  "Two answers of [[scan!]] combined: the greater height, and a draft where either reaches one."
  ^long [^long a ^long b]
  (cond (neg? a) b
        (neg? b) a
        :else (bit-or (max (bit-and a -2) (bit-and b -2)) (bit-and (bit-or a b) 1))))

(defn- queue? [x] (instance? clojure.lang.PersistentQueue x))

(defn- scanner
  "A function `(scan x at)` that adds to `found`, inner nodes first, each draft the walk
  reaches in `x`, each value of an unsealed type where `enter?`, and each value of a displaced
  definition of a sealed type, as `[at node height fields]`: `at` its path, last step first, and
  `fields` the keys of its fields in which a draft is reached. `at` is the path to `x`; a node
  in key position ends its path with `key-step`. The function returns what `x` reaches, as
  above."
  [key-step enter? ^java.util.ArrayList found]
  (letfn [(scan ^long [x at]
            ;; `in` scans `y` at the path `at` with `step` added, building that path only for a
            ;; collection
            (let [in (fn ^long [y step at] (if (coll? y) (scan y (cons step at)) -1))
                  node (fn ^long [x draft?]
                         (let [fields (java.util.ArrayList.)
                               r (long (reduce-kv (fn [r k v]
                                                    (let [rv (in v k at)]
                                                      (when (and (pos? rv) (== 1 (bit-and rv 1))) (.add fields k))
                                                      (reach r rv)))
                                                  -1 (if draft? (.-data ^Draft x) x)))
                               h (if (neg? r) 0 (inc (bit-shift-right r 1)))]
                           (.add found [at x h (vec fields)])
                           (bit-or (bit-shift-left h 1) (if draft? 1 (if (neg? r) 0 (bit-and r 1))))))]
              (cond (not (coll? x)) -1
                    (draft? x) (node x true)
                    (value? x) (cond (unsealed-value? x) (if enter? (node x false) -1)
                                     ;; a sealed value of a displaced definition fails where it
                                     ;; stands, and holds nothing the walk enters
                                     (displaced-value? x) (do (.add found [at x 0 []]) -1)
                                     :else -1)
                    (map-entry? x) (reach (in (key x) 0 at) (in (val x) 1 at))
                    (map? x) (reduce-kv (fn [r k v] (reach (reach r (in k key-step (cons k at))) (in v k at)))
                                        -1 x)
                    (set? x) (reduce (fn [r e] (reach r (in e e at))) -1 x)
                    (or (vector? x) (seq? x) (queue? x)) (loop [s (seq x), i 0, r -1]
                                                           (if s
                                                             (recur (next s) (inc i) (reach r (in (first s) i at)))
                                                             r))
                    :else -1)))]
    scan))

(defn- rebuild
  "`x` as the walk makes it: maps rebuilt as `clojure.walk` rebuilds them, keys and values;
  vectors, lists, sets and queues by element; a list a list, a queue and any other sequence a
  vector, each with its metadata; anything else as it is. Each draft and each value of a type it
  reaches is replaced by `(f it)`, and not entered."
  [x f]
  (let [go #(rebuild % f)]
    (cond (not (coll? x)) x
          (or (draft? x) (value? x)) (f x)
          (map-entry? x) (clojure.lang.MapEntry/create (go (key x)) (go (val x)))
          (instance? clojure.lang.IRecord x) (reduce (fn [r [k v]] (conj r [(go k) (go v)])) x x)
          (map? x) (into (empty x) (map (fn [[k v]] [(go k) (go v)])) x)
          (vector? x) (into (empty x) (map go) x)
          ;; a queue is a `list?`, so this clause stands before that one
          (queue? x) (with-meta-of (into [] (map go) x) x)
          (list? x) (with-meta-of (apply list (map go x)) x)
          (seq? x) (with-meta-of (into [] (map go) x) x)
          (set? x) (into (empty x) (map go) x)
          :else x)))

(def ^:private seal-refusals
  "The errors with which [[seal]] refuses a draft, as data rather than a bug in a check."
  #{:recognitum/undeclared-keys :recognitum/check-failed
    :recognitum/displaced-constructor :recognitum/not-a-type :recognitum/not-a-draft})

(defn- seal-or-refusal
  "`[value nil]`, the seal of draft `d`, or of a value of an unsealed type against `sel`, or
  `[nil ex-data]` where [[seal]] refuses it."
  [d sel]
  (try [(if (draft? d) (seal d) (seal d sel)) nil]
       (catch clojure.lang.ExceptionInfo e
         (if (contains? seal-refusals (:error (ex-data e))) [nil (ex-data e)] (throw e)))))

(defn- seal-level
  "Seals the drafts, and values of unsealed types, `ds`, each as [[seal]] would, the drafts
  against every check and the values against `sel`, with one run of the engine for those that
  have checks to run. Refuses each value of a displaced definition in `ds`, of a sealed type
  or an unsealed one, with the error `:recognitum/displaced`, and each other value whose type
  `sel`, not every, selects nothing in, as [[seal]] does, before any check runs. Returns
  `[value nil]` or `[nil ex-data]` for each, in order."
  [ds sel]
  (let [;; each type, to a predicate of its declared keys, or false where it is not current:
        ;; asked once per type
        per-type (java.util.IdentityHashMap.)
        declared?* (fn [t] (let [c (.get per-type t)]
                             (if (nil? c)
                               (let [c (and (current? t) (member-of (:keys t)))] (.put per-type t c) c)
                               c)))
        ;; whether seal refuses `d` before any check runs: a draft of no type or of a displaced
        ;; definition, or one holding a key its type does not declare; a value of a displaced
        ;; definition. A value of an unsealed type holds no undeclared key; one whose type `sel`
        ;; selects nothing in is `:nothing`.
        by-every (= select/every sel)
        refused (mapv (fn [d] (let [t (type-of d)
                                    declared? (when t (declared?* t))]
                                (cond (draft? d) (not (and declared? (all-declared? declared? (.-data ^Draft d))))
                                      (not declared?) true
                                      (and (not by-every) (nothing? t sel)) :nothing
                                      :else false)))
                      ds)
        every-plan [select/every nil]
        value-plan [sel :seal]
        answers (run-batch (if (some identity refused)
                             (vec (keep-indexed (fn [i d] (when-not (refused i) d)) ds))
                             ds)
                           (fn [t] (if (unsealed? t) value-plan every-plan)))]
    (loop [i 0, j 0, out (transient [])]
      (if (== i (count ds))
        (persistent! out)
        (let [d (ds i)]
          (if (refused i)
            (recur (inc i) j (conj! out (cond (= :nothing (refused i)) [nil (ex-data (selects-nothing-refusal (type-of d) sel))]
                                              (draft? d) (seal-or-refusal d sel)
                                              (unsealed-value? d) [nil (ex-data (displaced-unsealed (:name (type-of d)) d))]
                                              :else [nil (ex-data (displaced-refusal (:name (type-of d)) d))])))
            (let [a (answers j)]
              (recur (inc i) (inc j)
                     (conj! out (if (true? a) (seal-or-refusal d sel) [nil (ex-data (check-failed (type-of d) a))]))))))))))

(defn- seal-all*
  "Seals every draft that a walk of `shape` reaches, inner drafts first, all or nothing; where
  `enter?`, also enters and seals each value of an unsealed type against `sel`."
  [shape sel key-step enter?]
  (let [found (java.util.ArrayList.)
        _ ((scanner key-step enter? found) shape ())
        ;; each draft or value entered, to `[checked value fields]`: it as checked, holding the
        ;; walk's value of each field in which a draft is reached; its sealed value, or nil; and
        ;; those fields. A node given at two places is checked at each, alike.
        done (java.util.IdentityHashMap.)
        out (fn [x] (if-let [[checked v] (.get done x)] (or v checked) x))
        failures (java.util.ArrayList.)]
    (doseq [[_ level] (sort-by key (group-by #(nth % 2) found))]
      (let [;; a value of a displaced definition refuses writes: it is checked, and given back,
            ;; as it is
            level (mapv (fn [[at d n :as e]]
                          (if (or (draft? d) (current? (type-of d))) e [at d n []]))
                        level)
            ds (mapv (fn [[_ d _ fields]] (reduce (fn [x k] (assoc x k (rebuild (get d k) out))) d fields)) level)
            sealed (seal-level ds sel)]
        (dotimes [i (count ds)]
          (let [[at d _ fields] (level i)
                [v failure] (sealed i)]
            (when failure (.add failures [(vec (reverse at)) failure]))
            (.put done d [(ds i) v fields])))))
    (if (.isEmpty failures)
      (rebuild shape out)
      (let [drafts-of (fn drafts-of [x]
                        (if-let [[checked _ fields] (.get done x)]
                          (reduce (fn [y k] (assoc y k (rebuild (get x k) drafts-of))) checked fields)
                          x))
            failures (into {} failures)]
        (throw (ex-info (str (count failures) " of " (.size found) " drafts and values did not seal, at "
                             (str/join ", " (map pr-str (keys failures))))
                        {:error :recognitum/drafts-failed
                         :failures failures
                         :drafts (rebuild shape drafts-of)}))))))

(defn seal-all
  "Seals every draft that a walk of `shape` reaches, inner drafts first, all or nothing, and
  every value of an unsealed type, which the walk enters as a draft, against `sel` (every
  check where none is given). See `recognitum.core/seal-all`; `key-step` ends the path of a
  draft or value in key position."
  ([shape key-step] (seal-all* shape select/every key-step true))
  ([shape sel key-step] (seal-all* shape sel key-step true)))

(defn drafting-all
  "[[seal-all]] of `f` of `shape` with each sealed value the walk reaches opened as a draft.
  Values of unsealed types are neither opened, nor entered, nor sealed, and neither is a value
  of a displaced definition whose name names no current definition of its type: the seal
  reports it. See `recognitum.core/drafting-all`."
  [shape f key-step]
  (seal-all* (f (rebuild shape (fn [x] (if (or (unsealed-value? x) (orphan? x)) x (draft x)))))
             select/every key-step false))

(defn drafting
  "`f` of draft `v`, unsealed; or of a value `v`, the seal of `f` of its draft. See
  `recognitum.core/drafting`."
  [v f]
  (if (draft? v)
    (f v)
    (do (some->> (type-of v) (refuse-type! v))
        (seal (f (draft v))))))
