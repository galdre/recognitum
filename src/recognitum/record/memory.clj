(ns recognitum.record.memory
  "What a draft, or a value of an unsealed type, remembers: its memory, a `Memo` that holds the
  checks that passed on the entries it was made for (its base) and the keys written since.

  - [[passes]] answers the checks that a memory shows passing on given entries, and
    [[passes-mask]] answers the same as a mask.
  - A memory shows a check passing only on the strength of its proof: either the sealed value
    that is its base, which passes every check, or a draft of the proof strategy (what
    `recognitum.proof/open` makes, not a `recognitum.record.draft` draft) that the strategy
    confirms was marked with the matching `PassKey`. A memory shows nothing on entries that
    differ from its base at a key not written since: it was moved onto other entries.
  - A type's `Hot`, made by [[hot-of]], holds what these functions read of the type, and its
    masks where it has them: in a type of at most 64 checks, each check has a bit of a
    `long`, and [[mask-of]] and [[set-of]] turn a set of checks into the `long` of their bits
    and back.

  Hidden: the test that a memory was not moved, and the sets kept for masks."
  (:require
   [recognitum.proof :as proof]))

(def ^:private none (Object.))

(deftype ^:private PassKey [data passes mask]
  Object
  (equals [_ o] (and (instance? PassKey o) (identical? data (.-data ^PassKey o)) (= passes (.-passes ^PassKey o))
                     (= mask (.-mask ^PassKey o))))
  (hashCode [_] (unchecked-add-int (System/identityHashCode data) (hash passes))))

;; What a draft, or a value of an unsealed type, remembers: the checks `passes` that pass on
;; the entries of `base`, as `proof` shows, and the keys `written` since. `proof` is a sealed
;; value of `type` that is `base` itself, so every check passes (never of an unsealed type,
;; whose `Hot` names a class nothing is an instance of), or a draft of the proof strategy
;; marked with `(PassKey base passes mask)`; nil where nothing passes. `mask` is `passes` as a
;; mask, or nil for a type of more than 64 checks.
(deftype Memo [type base passes written proof mask])

;; What [[passes]] and [[passes-mask]] read of a type, in fields: its value class, its draft
;; class, its proof strategy, its check ids and each key's readers as a vector. A type of at
;; most 64 checks also gives each check a bit of a long: `bits` maps each id to its bit, `all`
;; has every bit, `readers-m` maps each key to the bits of its readers, `ids-v` holds the ids
;; by bit, and `sets` keeps the set of each mask asked for. Of a larger type these are nil.
(deftype ^:private Hot [vc dc strategy ids readers-v bits all readers-m ids-v ^java.util.concurrent.ConcurrentHashMap sets])

(defn hot-of
  "The `Hot` of a type: its value class `vc`, draft class `dc` and `strategy`, its check ids
  `ids`, and its readers, as `readers` (key to set of ids) and `readers-v` (key to vector of
  ids). It holds masks where `ids` has at most 64 checks."
  [vc dc strategy ids readers readers-v]
  (if (<= (count ids) 64)
    (let [ids-v (vec (sort-by str ids))
          bits (into {} (map-indexed (fn [i id] [id (bit-shift-left 1 i)])) ids-v)
          m-of (fn [xs] (reduce (fn [m id] (bit-or m (long (bits id)))) 0 xs))]
      (Hot. vc dc strategy ids readers-v bits (m-of ids-v) (update-vals readers m-of) ids-v
            (java.util.concurrent.ConcurrentHashMap.)))
    (Hot. vc dc strategy ids readers-v nil nil nil nil nil)))

(defn mask-of
  "The mask of the set of check ids `xs`, or nil for a type without masks."
  [^Hot hot xs]
  (when-let [bits (.-bits hot)]
    (let [it (.iterator ^Iterable xs)]
      (loop [m 0]
        (if (.hasNext it) (recur (bit-or m (long (bits (.next it))))) m)))))

(defn set-of
  "The set of check ids of `mask`, kept in `hot` for the next call while it has room."
  [^Hot hot ^long mask]
  (let [^java.util.concurrent.ConcurrentHashMap sets (.-sets hot)]
    (or (.get sets mask)
        (let [ids-v (.-ids-v hot)
              s (persistent! (reduce (fn [acc i] (if (bit-test mask i) (conj! acc (nth ids-v i)) acc))
                                     (transient #{}) (range (count ids-v))))]
          (when (< (.size sets) 1000) (.putIfAbsent sets mask s))
          s))))

(defn- written-since?
  "Whether every key whose entry differs between `base` and `data`, by identity, is in `written`."
  [base data written]
  (let [n (reduce-kv (fn [n k v]
                       (let [b (get base k none)]
                         (cond (identical? b v)       (inc n)
                               (contains? written k) (if (identical? b none) n (inc n))
                               :else                 (reduced -1))))
                     0 data)]
    (and (not (neg? n))
         (or (= n (count base))
             (every? #(or (contains? data %) (contains? written %)) (keys base))))))

(defn passes
  "The checks of `type` that the memory `mo` shows passing on the entries `data`: what its
  proof shows passing on its base, less the readers of each key written since. Shows nothing
  where `mo` is not a memory of `type`, and where `data` differs from the base at a key that
  `mo` does not record as written: the memory was moved onto other entries."
  [type data mo]
  (if-not (and (instance? Memo mo) (identical? type (.-type ^Memo mo)))
    #{}
    (let [^Memo mo mo
          ^Hot hot (:recognitum.record/hot type)
          base (.-base mo)
          proof (.-proof mo)
          p (cond (nil? proof) nil
                  (and (identical? proof base) (instance? ^Class (.-vc hot) proof)) (.-ids hot)
                  (and (instance? ^Class (.-dc hot) proof)
                       (proof/marked? (.-strategy hot) proof (PassKey. base (.-passes mo) (.-mask mo)))) (.-passes mo))
          w (.-written mo)]
      (if (and p (or (identical? base data) (written-since? base data w)))
        (let [readers (.-readers-v hot)
              it (.iterator ^Iterable w)]
          (loop [p p]
            (if (.hasNext it)
              (recur (reduce disj p (readers (.next it) [])))
              p)))
        #{}))))

(defn passes-mask
  "What [[passes]] answers, as a mask, for a type with masks."
  ^long [type data mo]
  (if-not (and (instance? Memo mo) (identical? type (.-type ^Memo mo)))
    0
    (let [^Memo mo mo
          ^Hot hot (:recognitum.record/hot type)
          base (.-base mo)
          proof (.-proof mo)
          p (cond (nil? proof) nil
                  (and (identical? proof base) (instance? ^Class (.-vc hot) proof)) (.-all hot)
                  (and (instance? ^Class (.-dc hot) proof)
                       (proof/marked? (.-strategy hot) proof (PassKey. base (.-passes mo) (.-mask mo)))) (.-mask mo))
          w (.-written mo)]
      (if (and p (or (identical? base data) (written-since? base data w)))
        (let [readers-m (.-readers-m hot)
              it (.iterator ^Iterable w)]
          (loop [p (long p)]
            (if (.hasNext it)
              (recur (bit-and-not p (long (readers-m (.next it) 0))))
              p)))
        0))))
