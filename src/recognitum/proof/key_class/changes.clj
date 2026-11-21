(ns recognitum.proof.key-class.changes
  "CHG, the function that a key-class value's changes call in place of its write:

  - [[changes-fn]] makes CHG for a change guard;
  - [[carry-fn]] makes CHG for an unsealed definition's carry.

  CHG answers a change as the flat pairs of what it alters, or nil where it alters nothing;
  the value makes the new value from those pairs. CHG holds no access key. [[removed]] is the
  strategy's marker for a removed key. Hidden: how a conj or a transient's changes are read
  into pairs, and the sentinel of an absent entry.")

(set! *warn-on-reflection* true)

;; The strategy's marker for a removed key: what a pair, a change guard's `changes` and a
;; write's `v` hold for a key that the change removes. No value holds it.
(defonce removed
  (reify Object (toString [_] "the removed key")))

(def ^:private none
  "What a lookup answers for a key a map lacks: an object no map holds."
  (Object.))

(defn- pair-change
  "`[k v]` as a change of `old`, flat, or nil where it changes nothing: `v` identical to
  `old`'s entry, or `removed` for a key `old` lacks."
  [^clojure.lang.ILookup old k v]
  (let [o (.valAt old k none)]
    (when-not (if (identical? v removed) (identical? o none) (identical? v o))
      (doto (object-array 2) (aset 0 k) (aset 1 v)))))

(defn- entries-change
  "The entries of `es` that change `old`, flat, or nil where none does. `es` is an iterator over
  the entries of a map of `n` entries, so no key comes twice. A value `removed` removes its
  key."
  [^clojure.lang.ILookup old n ^java.util.Iterator es]
  (let [a (object-array (* 2 n))]
    (loop [i 0]
      (if (.hasNext es)
        (let [^java.util.Map$Entry e (.next es)
              k (.getKey e) v (.getValue e)
              o (.valAt old k none)]
          (if (if (identical? v removed) (identical? o none) (identical? v o))
            (recur i)
            (do (aset a i k) (aset a (unchecked-inc i) v) (recur (unchecked-add i 2)))))
        (cond (zero? i) nil
              (== i (alength a)) a
              :else (java.util.Arrays/copyOf a i))))))

;; What a change transient calls on itself. `net` answers the pairs it holds that change the
;; value it was made from; persistent! hands the transient to that value's cons, which calls
;; `net`.
(definterface ^:private ChangeSlots
  (live [])
  (^long at [k])
  (now [k])
  (add [k v])
  (put [k v])
  (net [target]))

(defn- conj-change
  "What `(conj old o)` changes, flat, or nil, read as `APersistentMap.cons` reads `o`: an entry,
  a vector pair, or a seq of entries, a later entry of a key replacing an earlier one."
  [^clojure.lang.ILookup old o]
  (cond
    ;; persistent! of a transient over `old`, which hands itself
    (instance? ChangeSlots o) (.net ^ChangeSlots o old)
    (instance? java.util.Map$Entry o)
    (pair-change old (.getKey ^java.util.Map$Entry o) (.getValue ^java.util.Map$Entry o))
    (instance? clojure.lang.IPersistentVector o)
    (let [^clojure.lang.IPersistentVector o o]
      (when-not (== 2 (.count o))
        (throw (IllegalArgumentException. "Vector arg to map conj must be a pair")))
      (pair-change old (.nth o 0) (.nth o 1)))
    (instance? clojure.lang.IPersistentMap o)
    (entries-change old (count o) (.iterator ^Iterable o))
    :else
    (let [m (loop [m (transient {}) s (seq o)]
              (if s
                (let [^java.util.Map$Entry e (first s)] (recur (assoc! m (.getKey e) (.getValue e)) (next s)))
                (persistent! m)))]
      (entries-change old (count m) (.iterator ^Iterable m)))))

(deftype ^:private ChangeTransient [^clojure.lang.IPersistentCollection old
                                    ^:unsynchronized-mutable ^objects over
                                    ^:unsynchronized-mutable ^long size
                                    ^:unsynchronized-mutable ^long cnt
                                    ^:unsynchronized-mutable done]
  ;; `over` holds the pairs it was told, flat, each key once, the last value or `removed`
  ;; winning; `size` the slots used; `cnt` the count now
  clojure.lang.ITransientMap
  (assoc [this k v] (.put this k v) this)
  (without [this k]
    (.live this)
    (let [i (.at this k)
          o (if (neg? i) (.valAt ^clojure.lang.ILookup old k none) (aget over (inc i)))]
      (when-not (or (identical? o none) (identical? o removed))
        (set! cnt (dec cnt))
        (if (neg? i) (.add this k removed) (aset over (inc i) removed))))
    this)
  (conj [this o]
    (.live this)
    (cond (instance? java.util.Map$Entry o) (.put this (.getKey ^java.util.Map$Entry o) (.getValue ^java.util.Map$Entry o))
          (instance? clojure.lang.IPersistentVector o)
          (let [^clojure.lang.IPersistentVector o o]
            (when-not (== 2 (.count o))
              (throw (IllegalArgumentException. "Vector arg to map conj must be a pair")))
            (.put this (.nth o 0) (.nth o 1)))
          :else (loop [s (seq o)]
                  (when s
                    (let [^java.util.Map$Entry e (first s)] (.put this (.getKey e) (.getValue e)))
                    (recur (next s)))))
    this)
  (persistent [this]
    (.live this)
    (set! done true)
    (if (zero? size)
      old
      (.cons old this)))
  (count [this] (.live this) (int cnt))
  (valAt [this k] (.live this) (let [v (.now this k)] (if (identical? v none) nil v)))
  (valAt [this k nf] (.live this) (let [v (.now this k)] (if (identical? v none) nf v)))
  clojure.lang.ITransientAssociative2
  (containsKey [this k] (.live this) (not (identical? none (.now this k))))
  (entryAt [this k] (.live this) (let [v (.now this k)] (when-not (identical? v none) (clojure.lang.MapEntry/create k v))))
  ChangeSlots
  (live [_] (when done (throw (IllegalAccessError. "Transient used after persistent! call"))))
  (at [_ k]
    (loop [i 0]
      (cond (>= i size) -1
            (clojure.lang.Util/equiv k (aget over i)) i
            :else (recur (+ i 2)))))
  (now [this k]
    (let [i (.at this k)]
      (if (neg? i)
        (.valAt ^clojure.lang.ILookup old k none)
        (let [v (aget over (inc i))] (if (identical? v removed) none v)))))
  (add [_ k v]
    (when (== size (alength over))
      (set! over (java.util.Arrays/copyOf over (int (* 2 size)))))
    (aset over size k)
    (aset over (inc size) v)
    (set! size (+ size 2)))
  (net [_ target]
    ;; the pairs that change `old`, flat, or nil; only `old` itself takes them
    (when-not (identical? target old)
      (throw (IllegalArgumentException. "a transient's changes apply only to the value it was made from")))
    (let [a (object-array size)]
      (loop [i 0 j 0]
        (if (< i size)
          (let [k (aget over i) v (aget over (inc i)) o (.valAt ^clojure.lang.ILookup old k none)]
            (if (if (identical? v removed) (identical? o none) (identical? v o))
              (recur (+ i 2) j)
              (do (aset a j k) (aset a (inc j) v) (recur (+ i 2) (+ j 2)))))
          (cond (zero? j) nil
                (== j size) a
                :else (java.util.Arrays/copyOf a (int j)))))))
  (put [this k v]
    (.live this)
    (let [i (.at this k)
          o (if (neg? i) (.valAt ^clojure.lang.ILookup old k none) (aget over (inc i)))]
      (when (or (identical? o none) (identical? o removed)) (set! cnt (inc cnt)))
      (if (neg? i) (.add this k v) (aset over (inc i) v)))))

(defn- change-transient
  "A transient over `old` that keeps only what it is told. Its persistent! is one
  `(conj old this)`, and so one call of CHG with the net change, or `old` itself where it was
  told nothing. Reads answer as a transient over `old`'s map would."
  [^clojure.lang.IPersistentCollection old]
  (ChangeTransient. old (object-array 8) 0 (.count old) false))

(defn changes-fn
  "CHG for the change guard `cg`: the function that T's changes call in place of the write.

  - With `old` and the change (an item to `conj`, or a key and a value, the value [[removed]]
    for a removal), calls `(cg old changes)` and, where it returns, answers the change as flat
    pairs k, v. Where nothing changes, calls nothing and answers nil. T makes the new value
    from `old` and the pairs.
  - With `old` alone, answers a transient over `old`."
  [^clojure.lang.IFn cg]
  (let [guarded (fn [old ^objects ch]
                  (when ch
                    (.invoke cg old (clojure.lang.PersistentArrayMap. ch))
                    ch))]
    (fn
      ([old] (change-transient old))
      ([old o] (guarded old (conj-change old o)))
      ([old k v] (guarded old (pair-change old k v))))))

(defn carry-fn
  "CHG for the carry `carry` of an unsealed definition: as [[changes-fn]]'s, but where the
  change is not empty it answers the pairs followed by what `(carry old changes)` returned,
  which T's change takes as the new value's memory."
  [^clojure.lang.IFn carry]
  (let [carried (fn [old ^objects ch]
                  (when ch
                    (let [n (alength ch)
                          a (java.util.Arrays/copyOf ch (unchecked-inc-int n))]
                      (aset a n (.invoke carry old (clojure.lang.PersistentArrayMap. ch)))
                      a)))]
    (fn
      ([old] (change-transient old))
      ([old o] (carried old (conj-change old o)))
      ([old k v] (carried old (pair-change old k v))))))
