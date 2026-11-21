(ns recognitum.record.draft
  "The draft: an unchecked map of a type that remembers which checks pass on its entries and,
  at each write, forgets the checks that read a key written. A `Draft` holds its entries; its
  cell, an atom that holds its memory (a `recognitum.record.memory.Memo`); its metadata; and
  how many of its keys its type does not declare.

  - [[draft?]] answers whether a value is a draft, and [[marks-of]] answers a draft's memory;
  - [[rewritten]] makes the draft that a write gives;
  - [[odd-after]] counts the undeclared keys after a write of several keys;
  - [[changed-keys]] answers the keys that a write changed.

  Hidden: the count of undeclared keys kept at each write, the map methods, and the sentinel
  of an absent entry."
  (:require
   [recognitum.record.memory])
  (:import
   [recognitum.record.memory Memo]))

(def ^:private none (Object.))

(declare rewritten changed-keys odd-with odd-without odd-after)

;; A draft's entries `data`, its memory's cell, its metadata, and `odd`, how many of its keys its
;; type does not declare, counted at each write.
(deftype Draft [data cell mta ^long odd]
  clojure.lang.IPersistentMap
  (assoc [this k v] (let [old (get data k none)]
                      (if (identical? v old)
                        this
                        (rewritten this (assoc data k v) #(conj % k) (if (identical? old none) (odd-with this k) odd)))))
  (assocEx [this k v] (.assoc this k v))
  (without [this k] (if (contains? data k) (rewritten this (dissoc data k) #(conj % k) (odd-without this k)) this))
  clojure.lang.Associative
  (containsKey [_ k] (contains? data k))
  (entryAt [_ k] (find data k))
  clojure.lang.ILookup
  (valAt [_ k] (get data k))
  (valAt [_ k nf] (get data k nf))
  clojure.lang.Counted
  (count [_] (count data))
  clojure.lang.IPersistentCollection
  (cons [this o] (if (instance? clojure.lang.IMapEntry o)
                   (.assoc this (key o) (val o))
                   (let [y (conj data o)
                         ch (changed-keys data y)]
                     (if (empty? ch) this (rewritten this y #(into % ch) (odd-after this y ch))))))
  (empty [_] (throw (UnsupportedOperationException. "a draft has no empty value: use (rec/draft T)")))
  (equiv [_ o] (and (instance? Draft o) (= data (.-data ^Draft o))))
  clojure.lang.Seqable
  (seq [_] (seq data))
  java.lang.Iterable
  (iterator [_] (.iterator ^Iterable data))
  clojure.lang.IObj
  (withMeta [_ m] (Draft. data cell m odd))
  clojure.lang.IMeta
  (meta [_] mta)
  Object
  (hashCode [_] (hash data))
  (equals [this o] (.equiv this o)))

(defn- undeclared?
  "Whether the type of draft `d`'s memory does not declare `k`."
  [^Draft d k]
  (let [mo @(.-cell d)]
    (and (instance? Memo mo) (not (contains? (:keys (.-type ^Memo mo)) k)))))

(defn- odd-with
  "The number of keys that draft `d`'s type does not declare among `d`'s keys with `k` added,
  where `d` does not hold `k`."
  ^long [^Draft d k]
  (if (undeclared? d k) (inc (.-odd d)) (.-odd d)))

(defn- odd-without
  "The number of keys that draft `d`'s type does not declare among `d`'s keys with `k`
  removed, where `d` holds `k`."
  ^long [^Draft d k]
  (if (and (pos? (.-odd d)) (undeclared? d k)) (dec (.-odd d)) (.-odd d)))

(defn odd-after
  "The number of keys of `data` that draft `d`'s type does not declare, where `data` is `d`'s
  entries after a write of the keys `ks`: `d`'s count, less each such key the write removed,
  plus each it added."
  ^long [^Draft d data ks]
  (let [old (.-data d)]
    (reduce (fn [^long n k]
              (let [was (contains? old k)]
                (cond (= was (contains? data k)) n
                      (not (undeclared? d k)) n
                      was (dec n)
                      :else (inc n))))
            (.-odd d) ks)))

(defn rewritten
  "The draft that a write to draft `d` gives: it holds `data`, of whose keys `odd` are keys its
  type does not declare, and `d`'s metadata. Its memory is `d`'s, with the keys written that
  `add` returns from `d`'s keys written, so that it forgets the checks that read them. A
  memory with no proof, which shows nothing passing, is kept as it is."
  [^Draft d data add ^long odd]
  (let [mo @(.-cell d)]
    (Draft. data
            (atom (if (and (instance? Memo mo) (some? (.-proof ^Memo mo)))
                    (let [^Memo mo mo]
                      (Memo. (.-type mo) (.-base mo) (.-passes mo) (add (.-written mo)) (.-proof mo) (.-mask mo)))
                    mo))
            (.-mta d)
            odd)))

(defn draft?
  "Whether `x` is a draft."
  [x]
  (instance? Draft x))

(defn marks-of
  "The memory that draft `d`'s cell holds now."
  ^Object [d] @(.-cell ^Draft d))

(defn changed-keys
  "The keys whose entry differs between `old` and `new`: added, removed, or holding a value
  that is not identical."
  [old new]
  (let [shared (long-array 1)
        changed (reduce-kv (fn [acc k v]
                             (let [o (get old k none)]
                               (when-not (identical? o none) (aset shared 0 (inc (aget shared 0))))
                               (if (identical? v o) acc (conj acc k))))
                           #{} new)]
    (if (= (aget shared 0) (count old))
      changed
      (reduce (fn [acc k] (if (contains? new k) acc (conj acc k))) changed (keys old)))))
