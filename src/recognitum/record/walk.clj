(ns recognitum.record.walk
  "Walks of nested shapes: [[seal-all]] seals every draft that it reaches in a shape, and
  every value of an unsealed type, or seals none; [[drafting-all]] and [[drafting]] open
  sealed values as drafts, call a function, and seal what it returns."
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
  a sealed one. Not a proof: [[recognitum.record.values/sealed?]] and
  [[recognitum.record.values/proves?]] answer that."
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

;; What a scan, the function that [[scanner]] returns, answers of a part of a shape: -1 where
;; it holds no draft and no value the walk enters; else its height, shifted left one bit, with
;; the low bit set where a draft is reached in it. The height of a draft or an entered value is
;; one more than the greatest height of those it holds, or 0 where it holds none.

(defn- reach
  "Two answers of a scan combined: the greater height, with the low bit set where either has
  it."
  ^long [^long a ^long b]
  (cond (neg? a) b
        (neg? b) a
        :else (bit-or (max (bit-and a -2) (bit-and b -2)) (bit-and (bit-or a b) 1))))

(defn- queue? [x] (instance? clojure.lang.PersistentQueue x))

(defn- scanner
  "A scan: a function `(scan x at)`, where `at` is the path to `x`, last step first. It adds to
  `found`, inner nodes first, each node that the walk reaches in `x`: each draft, each value of
  an unsealed type where `enter?`, and each value of a displaced definition of a sealed type.
  A node is added as `[at node height fields]`: its path, itself, its height, and the keys of
  its fields in which a draft is reached. A node in key position ends its path with
  `key-step`. Returns its answer for `x`, as the comment above [[reach]] defines it."
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
  "`x` rebuilt with each draft and each value of a type that the walk reaches replaced by
  `(f it)`, which the walk does not enter:

  - a map, keys and values, as `clojure.walk` rebuilds it, so that a record stays a record;
  - a vector, a list or a set, element by element, as the same kind of collection;
  - a queue, or any other sequence, element by element, as a vector;
  - anything else, as it is.

  Every rebuilt collection keeps its metadata."
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
  "The `:error`s of a refusal by [[seal]] that [[seal-or-refusal]] returns as data; any other
  exception, such as one that a check body throws, propagates."
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
  "Seals each of `ds`, drafts and values, as [[seal]] would: a draft against every check, and
  a value of an unsealed type against `sel`. The checks of every element run together, in
  one run of the engine. Returns `[sealed nil]`, or `[nil ex-data]` of a refusal, for each
  element, in order. These are refused before any check runs:

  - a value of a displaced definition, of a sealed type or an unsealed one, with
    `:recognitum/displaced`;
  - a value of an unsealed type in which `sel`, other than every, selects nothing, with
    `:recognitum/selects-nothing`;
  - a draft that [[seal]] refuses before running a check, as [[seal]] refuses it."
  [ds sel]
  (let [;; each type, to a predicate of its declared keys, or false where it is not current:
        ;; asked once per type
        per-type (java.util.IdentityHashMap.)
        declared?* (fn [t] (let [c (.get per-type t)]
                             (if (nil? c)
                               (let [c (and (current? t) (member-of (:keys t)))] (.put per-type t c) c)
                               c)))
        ;; `refused`, for each of `ds`: true where seal refuses it before any check runs (a
        ;; draft of no type, of a displaced definition, or holding a key its type does not
        ;; declare; a value of a displaced definition), `:nothing` where `sel` selects nothing
        ;; in its type, else false. A value of an unsealed type holds no undeclared key.
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
  "Seals every draft that a walk of `shape` reaches, as [[seal-all]] states; enters and seals
  each value of an unsealed type against `sel` only where `enter?`."
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
  "Seals every draft that a walk of `shape` reaches, inner drafts first, and every value of an
  unsealed type, which the walk enters as it enters a draft, against `sel` (every check
  where none is given). `key-step` is the step that ends the path of a draft or value in key
  position. All or nothing:

  - where every one seals, returns `shape` with each replaced by its sealed value;
  - else throws `:recognitum/drafts-failed`, whose data holds `:failures`, a map from the
    path of each draft or value that did not seal to its refusal's data, and `:drafts`,
    `shape` with its drafts unsealed."
  ([shape key-step] (seal-all* shape select/every key-step true))
  ([shape sel key-step] (seal-all* shape sel key-step true)))

(defn drafting-all
  "Opens as a draft each value that a walk of `shape` reaches, calls `f` with the result, and
  seals what `f` returns as [[seal-all]] does, against every check. A value of a displaced
  definition opens as a draft of its type's current definition. Left as they are, neither
  opened, nor entered, nor sealed:

  - a value of an unsealed type;
  - a value of a displaced definition whose name names no current definition of its type.
    Where its type is sealed, the seal then refuses it as a value of a displaced
    definition."
  [shape f key-step]
  (seal-all* (f (rebuild shape (fn [x] (if (or (unsealed-value? x) (orphan? x)) x (draft x)))))
             select/every key-step false))

(defn drafting
  "Where `v` is a draft, `(f v)`, unsealed. Else the seal of `(f (draft v))`, which throws as
  [[draft]] and [[seal]] do; for a type's class or type map, throws
  `:recognitum/not-a-value`."
  [v f]
  (if (draft? v)
    (f v)
    (do (some->> (type-of v) (refuse-type! v))
        (seal (f (draft v))))))
