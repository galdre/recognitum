(ns recognitum.record
  "The record layer: types whose values read as maps and carry proof that their checks passed,
  drafts that remember which checks pass, checked writes, optional fields and closed types.
  [[define-type]] defines a type from compiled checks, a proof strategy and a check engine,
  and names neither; the rest of this namespace acts on values of any type it defined.

  A **sealed value** is a value of a type's class. The only paths to one run the type's
  checks: [[make]], [[seal]], and a write (`assoc`, `dissoc`, `conj`, `merge`, `into`) on a
  sealed value, which reruns the checks that read a key it changes and seals the result or
  throws. A **draft** is an unchecked map of a type that remembers which checks pass on its
  entries; a write to it forgets the checks that read a key written.

  A type defined with `:unsealed true` has no sealed values and no drafts. Its values are
  made and written without checks and carry, in place, what a draft remembers: the checks
  that passed on their entries. Such a value is never sealed; [[proves?]] asks its memory.

  Every type is closed: a sealed value refuses a key its type does not declare, and a draft
  holding one does not seal. A required field must be present in a sealed value.

  The key that mints a type's values and marks its drafts never leaves the closure
  [[define-type]] builds: it is reachable only through the type's installed write, its key
  guards and its change guard, each of which runs the checks it stands for."
  (:require
   [clojure.set :as set]
   [clojure.string :as str]
   [recognitum.proof :as proof]
   [recognitum.select :as select]))

;;; ------------------------------------------------------------------ drafts

(def ^:private none (Object.))

(deftype ^:private PassKey [data passes mask]
  Object
  (equals [_ o] (and (instance? PassKey o) (identical? data (.-data ^PassKey o)) (= passes (.-passes ^PassKey o))
                     (= mask (.-mask ^PassKey o))))
  (hashCode [_] (unchecked-add-int (System/identityHashCode data) (hash passes))))

;; What a draft remembers: the checks `passes` that pass on the entries of `base`, as `proof`
;; shows, and the keys `written` since. `proof` is a sealed value of `type` that is `base`
;; itself, so every check passes (never of an unsealed type, whose `Hot` names a class nothing is
;; an instance of), or a draft of the type's proof strategy marked with
;; `(PassKey base passes mask)`; nil where nothing passes. `mask` is `passes` as a mask (see
;; [[Hot]]), or nil for a type of more than 64 checks.
(deftype Memo [type base passes written proof mask])

;; What `passes` reads of a type, in fields: its value class, its draft class, its proof
;; strategy, its check ids and each key's readers as a vector. A type of at most 64 checks
;; also gives each check a bit of a long: `bits` maps each id to its bit, `all` has every
;; bit, `readers-m` maps each key to the bits of its readers, `ids-v` holds the ids by bit,
;; and `sets` keeps the set of each mask asked for. Of a larger type these are nil.
(deftype ^:private Hot [vc dc strategy ids readers-v bits all readers-m ids-v ^java.util.concurrent.ConcurrentHashMap sets])

(defn- hot-of
  "The `Hot` of a type with check ids `ids` and readers `readers` (key to set of ids)."
  [vc dc strategy ids readers readers-v]
  (if (<= (count ids) 64)
    (let [ids-v (vec (sort-by str ids))
          bits (into {} (map-indexed (fn [i id] [id (bit-shift-left 1 i)])) ids-v)
          m-of (fn [xs] (reduce (fn [m id] (bit-or m (long (bits id)))) 0 xs))]
      (Hot. vc dc strategy ids readers-v bits (m-of ids-v) (update-vals readers m-of) ids-v
            (java.util.concurrent.ConcurrentHashMap.)))
    (Hot. vc dc strategy ids readers-v nil nil nil nil nil)))

(defn- mask-of
  "The mask of the set of check ids `xs`, or nil for a type without masks."
  [^Hot hot xs]
  (when-let [bits (.-bits hot)]
    (let [it (.iterator ^Iterable xs)]
      (loop [m 0]
        (if (.hasNext it) (recur (bit-or m (long (bits (.next it))))) m)))))

(defn- set-of
  "The set of check ids of `mask`, kept for the next call where the type has kept fewer than
  a thousand."
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

(defn- passes
  "The checks a draft's memory `mo` shows passing on its entries `data`: what its proof shows
  passing on the entries it was set for, less the checks that read a key written since. A
  memory whose entries differ from `data` on a key it does not record as written was moved
  onto other entries, and shows nothing."
  [type data mo]
  (if-not (and (instance? Memo mo) (identical? type (.-type ^Memo mo)))
    #{}
    (let [^Memo mo mo
          ^Hot hot (::hot type)
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

(defn- passes-mask
  "What [[passes]] answers, as a mask, for a type with masks."
  ^long [type data mo]
  (if-not (and (instance? Memo mo) (identical? type (.-type ^Memo mo)))
    0
    (let [^Memo mo mo
          ^Hot hot (::hot type)
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

(declare rewritten changed-keys)

(deftype Draft [data cell mta]
  clojure.lang.IPersistentMap
  (assoc [this k v] (if (identical? v (get data k none)) this (rewritten this (assoc data k v) #(conj % k))))
  (assocEx [this k v] (.assoc this k v))
  (without [this k] (if (contains? data k) (rewritten this (dissoc data k) #(conj % k)) this))
  clojure.lang.Associative
  (containsKey [_ k] (contains? data k))
  (entryAt [_ k] (find data k))
  clojure.lang.ILookup
  (valAt [_ k] (get data k))
  (valAt [_ k nf] (get data k nf))
  clojure.lang.Counted
  (count [_] (count data))
  clojure.lang.IPersistentCollection
  (cons [this o] (let [y (conj data o)
                       ch (changed-keys data y)]
                   (if (empty? ch) this (rewritten this y #(into % ch)))))
  (empty [_] (throw (UnsupportedOperationException. "a draft has no empty value: use (rec/draft T)")))
  (equiv [_ o] (and (instance? Draft o) (= data (.-data ^Draft o))))
  clojure.lang.Seqable
  (seq [_] (seq data))
  java.lang.Iterable
  (iterator [_] (.iterator ^Iterable data))
  clojure.lang.IObj
  (withMeta [_ m] (Draft. data cell m))
  clojure.lang.IMeta
  (meta [_] mta)
  Object
  (hashCode [_] (hash data))
  (equals [this o] (.equiv this o)))

(defn- rewritten
  "A draft holding `data`, written from draft `d`: it remembers what `d` remembers, its keys
  written as `add` gives them from `d`'s. A memory where nothing passes stays as it is."
  [^Draft d data add]
  (let [mo @(.-cell d)]
    (Draft. data
            (atom (if (and (instance? Memo mo) (some? (.-proof ^Memo mo)))
                    (let [^Memo mo mo]
                      (Memo. (.-type mo) (.-base mo) (.-passes mo) (add (.-written mo)) (.-proof mo) (.-mask mo)))
                    mo))
            (.-mta d))))

(defn draft?
  "Whether `x` is a draft."
  [x]
  (instance? Draft x))

;;; ------------------------------------------------------------------ types of values

(defn- marks-of ^Object [d] @(.-cell ^Draft d))

(defn- answered-type
  "The type whose value class or draft class is `c`, as the class itself answers, or nil."
  [^Class c]
  (when-let [g (proof/gate-of c)]
    (let [t (g ::type nil nil)]
      (when (and (map? t) (or (identical? c (::class t)) (identical? c (::draft-class t))))
        t))))

(defonce ^:private class-types
  ;; each class, to a volatile holding the type its class answers once it answers one: a
  ;; class's answer never changes once given, and nil may yet become a type
  (proxy [java.lang.ClassValue] []
    (computeValue [_] (volatile! nil))))

(defn- type-of-class
  "The type whose value class or draft class is `c`, as the class itself answers, or nil. The
  answer is kept on the class once given, so it leaves nothing behind that would keep the
  class loaded."
  [^Class c]
  (let [held (.get ^java.lang.ClassValue class-types c)]
    (or @held
        (when-let [t (answered-type c)]
          (vreset! held t)))))

(defn- draft-type
  "The type of a draft's memory `mo`, where that type's own gate answers it, or nil: a memory
  built by hand around a type map that no definition made names no type."
  [mo]
  (when (instance? Memo mo)
    (let [t (.-type ^Memo mo)
          g (when (map? t) (::gate t))]
      (when (volatile? g)
        (when-let [g @g]
          (when (identical? t (g ::type nil nil)) t))))))

(defn type-of
  "The type `x` belongs to: a type's value class, a sealed value, a draft, or a type itself.
  Nil for anything else."
  [x]
  (cond (class? x)  (type-of-class x)
        (draft? x)  (draft-type (marks-of x))
        ;; a sorted map's comparator may refuse the key, and no type is a sorted map
        (and (map? x) (not (sorted? x)) (contains? x ::class)) x
        (nil? x)    nil
        :else       (type-of-class (class x))))

(defn- type-of! [x]
  (or (type-of x)
      (throw (ex-info (str "not a value, a draft or a class of a recognitum type: " (pr-str x))
                      {:error :recognitum/not-a-type :value x}))))

(defn- refuse-type!
  "Refuses `x` where `x` is `t`'s class or `t` itself, a type given where a value belongs."
  [x t]
  (when (or (class? x) (identical? x t))
    (throw (ex-info (str "a type was given where a value belongs: " (:name t))
                    {:error :recognitum/not-a-value :type (:name t)}))))

(defn- value-type!
  "The type of `x`, a value or a draft; refuses anything else, a type included."
  [x]
  (let [t (type-of! x)]
    (refuse-type! x t)
    t))

(defn- gate
  "The type's installed write. Each arity runs the checks it stands for. [[define-type]] keeps
  it in the type once installed; a type without it asks the strategy."
  [type]
  (or (when-let [g (::gate type)] (.deref ^clojure.lang.Volatile g))
      (proof/installed (:strategy type) (::class type))))

(defn- current?
  "Whether `type` is the current definition of its name: no later definition displaced it."
  [type]
  ((gate type) ::current? nil nil))

(defn named-now
  "The type that the namespace of type name `n` maps its name to, if it is a definition of
  `n`, current or not."
  [n]
  (let [c (some-> (find-ns (symbol (namespace n))) (.getMapping (symbol (name n))))]
    (when (class? c)
      (when-let [t (type-of-class c)]
        (when (= n (:name t)) t)))))

(defn- types-in
  "The current types that namespace `n` defines: each its namespace maps its name to."
  [n]
  (for [[s c] (ns-imports n)
        :let [t (type-of-class c)]
        :when (and t (= (:name t) (symbol (str (ns-name n)) (str s))) (current? t))]
    t))

(defn current-types
  "Each type name, to the type it names now: the current definition that the name's namespace
  maps the name to."
  []
  (into {} (for [n (all-ns), t (types-in n)] [(:name t) t])))

(defn refuse-unnamed!
  "Refuses selection `sel` where a keyword in it names no concern or bundle check (see
  [[recognitum.select/named]]) and no check of a current type of the keyword's namespace.
  Returns `sel`."
  [sel]
  (doseq [k (select/keywords sel)]
    (when-not (or (select/named k)
                  (some #(contains? (:ids %) k) (some-> (namespace k) symbol find-ns types-in)))
      (throw (ex-info (str "no concern, bundle check or check of a type is named " k)
                      {:error :recognitum/unknown-name :name k}))))
  sel)

(defn- print-value
  "Prints a value of any type, current or displaced, as its tagged literal."
  [v ^java.io.Writer w]
  ;; the value printed as a map, without its meta, as `into {}` of it would print, but with no
  ;; map built
  (let [as-map (get-method print-method clojure.lang.IPersistentMap)]
    (when-let [t (type-of-class (class v))]
      (.write w (str "#" (:name t) " ")))
    (as-map (with-meta v nil) w)))

(.addMethod ^clojure.lang.MultiFn print-method recognitum.proof.Proven print-value)

(prefer-method print-method recognitum.proof.Proven clojure.lang.IPersistentMap)
(prefer-method print-method recognitum.proof.Proven java.util.Map)

(defmethod print-method Draft [^Draft d ^java.io.Writer w]
  (.write w (str "#recognitum/draft [" (:name (type-of d)) " "))
  (print-method (.-data d) w)
  (.write w "]"))

;;; ------------------------------------------------------------------ reports

(defn- blocked-by
  "The checks in `blocked` that did not run because `id` failed: those waiting on it, directly
  or through another check in `blocked`."
  [type id blocked]
  (loop [acc #{}]
    (let [more (into acc (filter (fn [b] (some #(or (= id %) (acc %)) (get-in type [:by-id b :waits]))))
                     blocked)]
      (if (= more acc) acc (recur more)))))

(defn- pulled-back
  "For each failed or blocked check that an `except` in `sel` removed but a wait pulled back
  in: the checks that wait on it, and why it ran."
  [type sel picked to-run ids]
  (let [ex (select/excepted type sel)]
    (into {} (for [id ids
                   :when (and (contains? ex id) (not (contains? picked id)))
                   :let [ws (set (for [w to-run :when (contains? (get-in type [:by-id w :waits]) id)] w))
                         names (str/join ", " (sort ws))]]
               [id {:waited-on-by ws
                    :hint (str id " ran although an except removed it, because " names
                               (if (next ws) " wait" " waits") " on it, and a check runs whenever a"
                               " check that waits on it runs. To leave it out, also remove " names ".")}]))))

(defn- report
  "The report of a run: nil where nothing failed or was blocked, else `{:failed :blocked}`, each
  failed check's entry holding its failure `:data`, its `:doc`, and the checks it `:blocked`."
  ([type result] (report type result nil))
  ([type {:keys [failed blocked]} pull]
   (when (or (seq failed) (seq blocked))
     (cond-> {:failed (into {} (for [[id data] failed]
                                 [id (cond-> {:data data :blocked (blocked-by type id blocked)}
                                       (get-in type [:by-id id :doc]) (assoc :doc (get-in type [:by-id id :doc])))]))
              :blocked blocked}
       pull (as-> r (let [pb (pull (concat (keys failed) blocked))]
                      (cond-> r (seq pb) (assoc :pulled-back pb))))))))

(defn- show [x]
  (if (instance? Throwable x)
    (str "#error[" (.getName (class x)) " " (pr-str (ex-message x)) "]")
    (pr-str x)))

(defn- failure-message [type {:keys [failed blocked pulled-back missing]}]
  (str (:name type)
       (when (or (seq failed) (seq blocked) (empty? missing))
         (str " failed " (count failed) (if (= 1 (count failed)) " check" " checks")))
       (when (seq missing)
         (str (when (or (seq failed) (seq blocked)) " and") " lacks the required field"
              (when (next missing) "s") " " (str/join ", " (map pr-str (sort missing)))))
       (when (and (empty? failed) (seq blocked)) (str "; blocked: " (str/join ", " (sort blocked))))
       (apply str (for [[id {:keys [data doc blocked]}] (sort-by key failed)]
                    (str "\n  " id (when doc (str " (" doc ")")) ": " (show data)
                         (when (seq blocked) (str ", which blocked " (str/join ", " (sort blocked)))))))
       (apply str (for [[_ {:keys [hint]}] (sort-by key pulled-back)] (str "\n  " hint)))))

(defn- displaced-refusal
  "The refusal of a write to `v`, or of a method called with it, where `v` is a value of the type
  named `tname` and a later definition has displaced the one `v` belongs to."
  [tname v]
  (ex-info (str tname " was redefined: this value is of an earlier definition, so it is not"
                " sealed and refuses writes and its type's methods. To prove it under the current"
                " definition: (rec/seal (rec/draft v))")
           {:error :recognitum/displaced :type tname :value v}))

(defn- displaced-unsealed
  "The refusal of a write, a method or a run of checks on `v`, a value of the unsealed type
  named `tname`, where a later definition has displaced the one `v` belongs to."
  [tname v]
  (ex-info (str tname " was redefined: this value is of an earlier definition, so it proves nothing"
                " and refuses writes, its type's methods and every run of checks. To make a value of"
                " the current definition: (" (namespace tname) "/map->" (name tname) " (into {} v))")
           {:error :recognitum/displaced :type tname :value v}))

(defn- no-drafts
  "The refusal to open, clean or draft anything of the unsealed type named `tname`."
  [tname]
  (ex-info (str tname " has no drafts: its values check nothing when made or written, and remember"
                " in place what passed. Make one with " (namespace tname) "/map->" (name tname)
                ", and run its checks with rec/check or rec/seal")
           {:error :recognitum/no-drafts :type tname}))

(defn- no-definition
  "The refusal to draft `v`, a value of a displaced definition of the type named `tname`, where
  that name no longer names a current definition of the type."
  [tname v]
  (ex-info (str tname " has no current definition: this value is of a displaced definition, and"
                " its name no longer names a definition of the type, so it has no drafts")
           {:error :recognitum/no-current-definition :type tname :value v}))

(defn- displaced-constructor
  "The refusal of a constructor of the type named `tname`, held from before a later definition
  displaced the one it makes. `remedy`, if given, says what to call instead of the current
  `map->T`."
  [tname remedy]
  (ex-info (str tname " was redefined: this constructor is of an earlier definition and makes"
                " nothing. "
                (or remedy (str "Call the current " (namespace tname) "/map->" (name tname))))
           {:error :recognitum/displaced-constructor :type tname}))

(defn- displaced-draft
  "The refusal to seal a draft of the type named `tname`, opened from the class of a definition
  that a later one displaced."
  [tname]
  (let [n (namespace tname), t (name tname)]
    (ex-info (str tname " was redefined: this draft is of an earlier definition and seals nothing."
                  " Make a value of the current definition with " n "/map->" t ", or seal a draft of"
                  " the class " n " now names " t ": (rec/seal (into (rec/draft " t ") m))")
             {:error :recognitum/displaced-constructor :type tname})))

(defn- check-failed
  "The failure of a seal, a constructor or a write of `type`: the report `rep` of the checks that
  failed, or none, and under `:missing` the required fields `absent`, where any is."
  ([type rep] (check-failed type rep nil))
  ([type rep absent]
   (let [rep (cond-> (or rep {:failed {} :blocked #{}})
               absent (assoc :missing absent))]
     (ex-info (failure-message type rep)
              (assoc rep :error :recognitum/check-failed :type (:name type))))))

(defn- refuse-undeclared!
  "Refuses the keys of `ks` that `type` does not declare; where `data` is given, only those
  `data` holds."
  ([type ks] (refuse-undeclared! type ks nil))
  ([type ks data]
   (let [declared (:keys type)
         bad? (fn [k] (and (not (contains? declared k)) (or (nil? data) (contains? data k))))]
     (when (reduce (fn [_ k] (if (bad? k) (reduced true) false)) false ks)
       (let [bad (filter bad? ks)]
         (throw (ex-info (str (:name type) " has no field " (str/join ", " (map pr-str (sort-by str bad)))
                              ". Its fields: " (str/join " " (map :key (:fields type))))
                         {:error :recognitum/undeclared-keys :type (:name type) :keys (set bad)})))))))

(defn- all-declared?
  "Whether `declared?` holds of every key of map `m`."
  [declared? m]
  (reduce-kv (fn [_ k _] (if (declared? k) true (reduced false))) true m))

(defn- member-of
  "A predicate of whether `x` is in the set `xs`. Where `xs` holds a few keywords, which are
  interned, it compares by identity, without hashing."
  [xs]
  (if (and (<= (count xs) 16) (every? keyword? xs))
    (let [^objects a (object-array xs)
          n (alength a)]
      (fn [x] (loop [i 0] (cond (== i n) false (identical? x (aget a i)) true :else (recur (inc i))))))
    (fn [x] (contains? xs x))))

(defn- missing
  "The set of the required fields of `type` that `data` does not hold, or nil where it holds
  each. A required field's presence is a check of its own, with no name."
  [type data]
  (when-not (reduce (fn [_ k] (if (contains? data k) true (reduced false))) true (::required-v type))
    (into #{} (remove #(contains? data %)) (::required-v type))))

;;; ------------------------------------------------------------------ running checks

(def ^:dynamic ^:private *overrides*
  "The overrides of the probe whose checks run on this thread: a map from a source to the
  function that answers in its place. Nil outside a probe, and in any other run, even one a
  check body starts inside a probe."
  nil)

(defn sourced
  "The function a check's read of `src` calls: `src`, or the override the probe running the
  check gave for it. The define layer writes every `(&fetch src k)` and `(&fetch-each src ks)`
  of a check body as a read of `(sourced src)`."
  [src]
  (let [o *overrides*]
    (if (nil? o) src (get o src src))))

(def ^:private engine-passed
  "A run's result where nothing failed and nothing was blocked."
  {:failed {} :blocked #{}})

(defn- run-all-plain
  "`(run-all items)` with no probe's overrides in force: a run started inside a probe's check
  body reads its sources themselves."
  [run-all items]
  (if (nil? *overrides*)
    (run-all items)
    (binding [*overrides* nil] (run-all items))))

(defn- run
  "The result of running every check of `type` on `data` except those in `assumed`."
  [type data assumed]
  ((::run type) data assumed))

(defn- minus
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

(defn- passed-in
  "The checks of `to-run` that passed in `result`."
  [to-run {:keys [failed blocked]}]
  (reduce disj (set/difference to-run blocked) (keys failed)))

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

(defn bound-check
  "A compiled check of a bundle, run in a type: `run` given the map from each input key to
  what its input clause in `inputs` (a map from input key to a function of the value)
  answers. `inputs` holds the clauses of the inputs the check reads, and each runs only when
  the check runs. An input whose clause reads an absent field is absent."
  [run inputs]
  (fn [value]
    (run (reduce-kv (fn [m k f]
                      (let [x (try (f value)
                                   (catch clojure.lang.ExceptionInfo e
                                     (if (contains? (ex-data e) :recognitum.checks/absent) ::absent (throw e))))]
                        (if (= ::absent x) m (assoc m k x))))
                    {} inputs))))

(defn- with-meta-of
  "`m` with the meta of `x`: `m` itself where it holds that meta already."
  [m x]
  (let [mx (meta x)]
    (if (identical? mx (meta m)) m (with-meta m mx))))

(defn- present-only
  "`run`, where the field `k` is present; passing where it is absent."
  [k run]
  (fn [value] (if (contains? value k) (run value) true)))

;;; ------------------------------------------------------------------ one-key writes

(defn whole
  "The map `old` with `k` set to `v`, built as a map with `old`'s meta."
  [old k v]
  (with-meta (assoc (into {} (seq old)) k v) (meta old)))

(defmacro view-type
  "Defines the class named `cname` (a simple symbol, in the current namespace) of the view a
  one-key write's checks read: the map `old` with `k` set to `v`. A read of a key answers
  without building that map, and anything else builds it. A definition places this form in
  its expansion, so each type's view is a class of its own and its reads of `old` keep a
  profile per type."
  [cname]
  (let [full (symbol (str (namespace-munge *ns*) "." cname))
        [old k v x nf a b o f init args] (map #(gensym (name %)) '[old k v x nf a b o f init args])
        old (with-meta old {:tag 'clojure.lang.IPersistentMap})
        w `(whole ~old ~k ~v)]
    `(deftype* ~(symbol (str *ns*) (str cname)) ~full [~old ~k ~v]
       :implements [clojure.lang.ILookup clojure.lang.IPersistentMap clojure.lang.MapEquivalence
                    clojure.lang.IHashEq clojure.lang.IKVReduce clojure.lang.IFn java.util.Map
                    java.lang.Iterable clojure.lang.IMeta clojure.lang.IType]
       (~'valAt [this# ~x] (if (identical? ~x ~k) ~v (.valAt ~old ~x)))
       (~'valAt [this# ~x ~nf] (if (identical? ~x ~k) ~v (.valAt ~old ~x ~nf)))
       (~'containsKey [this# ~x] (or (identical? ~x ~k) (.containsKey ~old ~x)))
       (~'entryAt [this# ~x] (if (identical? ~x ~k) (clojure.lang.MapEntry/create ~k ~v) (.entryAt ~old ~x)))
       (~'assoc [this# ~a ~b] (assoc ~w ~a ~b))
       (~'assocEx [this# ~a ~b] (.assocEx ~(with-meta w {:tag 'clojure.lang.IPersistentMap}) ~a ~b))
       (~'without [this# ~a] (dissoc ~w ~a))
       (~'count [this#] (count ~w))
       (~'cons [this# ~o] (conj ~w ~o))
       (~'empty [this#] (with-meta {} (meta ~old)))
       (~'equiv [this# ~o] (= ~w ~o))
       (~'seq [this#] (seq ~w))
       (~'hasheq [this#] (hash ~w))
       (~'kvreduce [this# ~f ~init] (reduce-kv ~f ~init ~w))
       (~'invoke [this# ~x] (.valAt this# ~x))
       (~'invoke [this# ~x ~nf] (.valAt this# ~x ~nf))
       (~'applyTo [this# ~args] (clojure.lang.AFn/applyToHelper this# ~args))
       (~'size [this#] (count ~w))
       (~'isEmpty [this#] false)
       (~'get [this# ~x] (.valAt this# ~x))
       (~'containsValue [this# ~x] (.containsValue ~(with-meta w {:tag 'java.util.Map}) ~x))
       (~'keySet [this#] (.keySet ~(with-meta w {:tag 'java.util.Map})))
       (~'values [this#] (.values ~(with-meta w {:tag 'java.util.Map})))
       (~'entrySet [this#] (.entrySet ~(with-meta w {:tag 'java.util.Map})))
       (~'put [this# ~a ~b] (throw (UnsupportedOperationException.)))
       (~'remove [this# ~a] (throw (UnsupportedOperationException.)))
       (~'putAll [this# ~a] (throw (UnsupportedOperationException.)))
       (~'clear [this#] (throw (UnsupportedOperationException.)))
       (~'iterator [this#] (.iterator ~(with-meta w {:tag 'java.lang.Iterable})))
       (~'meta [this#] (meta ~old))
       (~'toString [this#] (str ~w))
       (~'hashCode [this#] (.hashCode ~(with-meta w {:tag 'java.lang.Object})))
       (~'equals [this# ~o] (.equals ~(with-meta w {:tag 'java.lang.Object}) ~o)))))

;; The view of the types that place no view of their own.
(view-type With)

(defmacro guard-maker
  "The form of a function of `current`, a key's run `r`, the key `k`, `clean?` and `refuse`
  that answers the key's guard: it calls `(refuse old nil)` where `current` holds false, runs
  `r` on the view of `old` with `k` set to `v`, an instance of the class [[view-type]] named
  `cname` defines, and calls `(refuse old result)` where the result is not clean. Without
  `cname`, the form defines a view class of its own first. A definition places this form in
  its expansion, so each type's guards and view are code of their own and their calls keep a
  profile per type."
  ([]
   (let [cname (gensym "View")]
     `(do (view-type ~cname)
          (guard-maker ~cname))))
  ([cname]
   (let [full (symbol (str (namespace-munge *ns*) "." cname))]
     `(fn* [current# r# k# clean?# refuse#]
        (fn* [old# v#]
          (when-not (.deref ^clojure.lang.Volatile current#) (refuse# old# nil))
          (let [result# (r# (new ~full old# k# v#) nil)]
            (when-not (clean?# result#) (refuse# old# result#))))))))

;;; ------------------------------------------------------------------ changes

(defmacro change-guard-maker
  "The form of a function of `own!`, `key-guards` (an IdentityHashMap from each declared key to
  its guard, or to `none` where its readers read a source), `removed`, `none`, `many` and
  `whole` that answers the change guard `(cg old changes)`: it calls `(own! old)`; a change
  that sets one key with a guard calls that guard, one with `none` calls `(whole old changes
  false)`, and any other calls `(many old changes)`. A definition places this form in its
  expansion, so each type's change guard is code of its own and its calls keep a profile per
  type."
  []
  (let [t (fn [tag s] (with-meta (gensym s) {:tag tag}))
        own (t 'clojure.lang.IFn "own") many (t 'clojure.lang.IFn "many") whole (t 'clojure.lang.IFn "whole")
        kg (t 'java.util.IdentityHashMap "key-guards") changes (t 'clojure.lang.IPersistentMap "changes")
        e (t 'java.util.Map$Entry "e") g (t 'clojure.lang.IFn "g")
        [removed none old v] (map gensym ["removed" "none" "old" "v"])]
    `(fn* [~own ~kg ~removed ~none ~many ~whole]
       (fn* [~old ~changes]
         (.invoke ~own ~old)
         (if (== 1 (.count ~changes))
           (let [~e (.next (.iterator ~(with-meta changes {:tag 'java.lang.Iterable})))
                 ~v (.getValue ~e)
                 ~g (when-not (identical? ~v ~removed) (.get ~kg (.getKey ~e)))]
             (cond (nil? ~g) (.invoke ~many ~old ~changes)
                   (identical? ~g ~none) (.invoke ~whole ~old ~changes false)
                   :else (.invoke ~g ~old ~v)))
           (.invoke ~many ~old ~changes))))))

(defn- applied
  "The map `old` with `changes` applied, built as a map with `old`'s meta: each key of
  `changes` set to its value, or removed where its value is `removed`."
  [old changes removed]
  (reduce-kv (fn [m k v] (if (identical? v removed) (dissoc m k) (assoc m k v)))
             (proof/plain-map old) changes))

(deftype ^:private Changed [^clojure.lang.IPersistentMap old ^clojure.lang.IPersistentMap changes removed]
  ;; The view a change's checks read: the map `old` with `changes` applied, as [[applied]]
  ;; builds it. A read of a key answers without building that map, and anything else builds it.
  clojure.lang.ILookup
  (valAt [this x] (.valAt this x nil))
  (valAt [_ x nf] (let [v (.valAt changes x none)]
                    (cond (identical? v none)    (.valAt old x nf)
                          (identical? v removed) nf
                          :else                  v)))
  clojure.lang.IPersistentMap
  (containsKey [_ x] (let [v (.valAt changes x none)]
                       (if (identical? v none) (.containsKey old x) (not (identical? v removed)))))
  (entryAt [this x] (when (.containsKey this x) (clojure.lang.MapEntry/create x (.valAt this x))))
  (assoc [_ a b] (assoc (applied old changes removed) a b))
  (assocEx [_ a b] (.assocEx ^clojure.lang.IPersistentMap (applied old changes removed) a b))
  (without [_ a] (dissoc (applied old changes removed) a))
  (count [_] (count (applied old changes removed)))
  (cons [_ o] (conj (applied old changes removed) o))
  (empty [_] (with-meta {} (meta old)))
  (equiv [_ o] (= (applied old changes removed) o))
  (seq [_] (seq (applied old changes removed)))
  (iterator [_] (.iterator ^Iterable (applied old changes removed)))
  clojure.lang.MapEquivalence
  clojure.lang.IHashEq
  (hasheq [_] (hash (applied old changes removed)))
  clojure.lang.IKVReduce
  (kvreduce [_ f init] (reduce-kv f init (applied old changes removed)))
  clojure.lang.IFn
  (invoke [this x] (.valAt this x))
  (invoke [this x nf] (.valAt this x nf))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))
  java.util.Map
  (size [_] (count (applied old changes removed)))
  (isEmpty [_] (zero? (count (applied old changes removed))))
  (get [this x] (.valAt this x))
  (containsValue [_ x] (.containsValue ^java.util.Map (applied old changes removed) x))
  (keySet [_] (.keySet ^java.util.Map (applied old changes removed)))
  (values [_] (.values ^java.util.Map (applied old changes removed)))
  (entrySet [_] (.entrySet ^java.util.Map (applied old changes removed)))
  (put [_ _ _] (throw (UnsupportedOperationException.)))
  (remove [_ _] (throw (UnsupportedOperationException.)))
  (putAll [_ _] (throw (UnsupportedOperationException.)))
  (clear [_] (throw (UnsupportedOperationException.)))
  clojure.lang.IMeta
  (meta [_] (meta old))
  Object
  (toString [_] (str (applied old changes removed)))
  (hashCode [_] (.hashCode ^Object (applied old changes removed)))
  (equals [_ o] (.equals ^Object (applied old changes removed) o)))

;;; ------------------------------------------------------------------ definition

(defn- run-jobs
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

(defn- in-group-order
  "`entries` in the order a group's run takes them: those with no `:type` first, as they
  stand, then those of each type, the types in the order `group-by` gives them where the
  entries are taken by their `:i`, ascending."
  [entries]
  (let [typed (filterv :type entries)]
    (if (every? #(identical? (:type (first typed)) (:type %)) typed)
      entries
      (into (filterv (complement :type) entries)
            (mapcat identity)
            (vals (group-by :type (sort-by :i typed)))))))

(defn waits-of
  "Each check of `checks` (each `{:id :waits :reads :shape-of}`), to every check it waits on:
  those its `:waits` names, and the shape check of each key it `:reads`, other than itself."
  [checks]
  (let [shape-id (into {} (keep (fn [c] (when-let [k (:shape-of c)] [k (:id c)]))) checks)]
    (into {} (for [{:keys [id waits reads]} checks]
               [id (into (set waits) (comp (keep shape-id) (remove #{id})) reads)]))))

(defn- compile-type
  [{:keys [name fields checks]} strategy define run-all runner]
  (let [optional (set (keep #(when (:optional? %) (:key %)) fields))
        checks (let [w (waits-of checks)] (mapv (fn [c] (assoc c :waits (w (:id c)))) checks))
        by-id (into {} (map (juxt :id identity)) checks)
        engine (define (into {} (for [{:keys [id waits shape-of gate run]} checks]
                                  [id {:after waits
                                       :body (cond->> run
                                               (contains? optional shape-of) (present-only shape-of)
                                               gate (present-only gate))}])))
        n-ids (count by-id)
        fetching (vec (keep #(when (:fetches? %) (:id %)) checks))
        ;; the checks that read no source, run on the calling thread
        pure (runner engine (remove (set fetching) (map :id checks)))]
    {:name     name
     :fields   (mapv #(select-keys % [:key :sym :optional?]) fields)
     :keys     (set (map :key fields))
     :optional optional
     :required (set (remove optional (map :key fields)))
     ::required-v (vec (remove optional (map :key fields)))
     ;; each selection, to the required fields whose presence it asks
     ::asked (java.util.concurrent.ConcurrentHashMap.)
     :checks   (mapv #(dissoc % :run) checks)
     :by-id    (update-vals by-id #(dissoc % :run))
     :ids      (set (keys by-id))
     :readers  (apply merge-with into {} (for [c checks, k (:reads c)] {k #{(:id c)}}))
     ;; each key, to the checks that read it, as a vector, which reduces without a seq
     ::readers-v (apply merge-with into {} (for [c checks, k (:reads c)] {k [(:id c)]}))
     :strategy strategy
     :run-all  run-all
     :engine   engine
     ;; every check but those in `assumed`, through the runner where every check left reads no
     ;; source
     ::run     (fn [data assumed]
                 (cond (= (count assumed) n-ids)
                       {:failed {} :blocked #{}}
                       (reduce (fn [_ id] (if (contains? assumed id) true (reduced false))) true fetching)
                       (pure data assumed)
                       :else
                       (nth (run-all-plain run-all [[engine data assumed]]) 0)))}))

(defn class-name
  "The name of the class of the values of the type named `type-name`, a qualified symbol, as
  `strategy` names it under every definition of the type."
  ^String [strategy type-name]
  (proof/class-name strategy type-name))

(defn refusal
  "Nil where `strategy` would define a type whose values implement `interfaces` with methods of
  `signatures`, as [[define-type]] takes them, else the strategy's refusal of that definition:
  a map with `:kind`, `:message`, and, by kind, `:method` (`[name arity]`, the name a symbol
  spelled as the signature spells it) or `:interfaces`.
  Asked before the methods' functions exist: each signature is passed with a placeholder
  function. `recognitum.define` gives its own message, at the method's line, for the kind
  `:map-method` where `:method` names a method of the definition; for every other kind it
  gives `:message`."
  [strategy interfaces signatures]
  (proof/refusal strategy {:interfaces (vec interfaces)
                           :methods (into {} (map (fn [sig] [sig (fn [& _])])) signatures)}))

(defn define-type
  "Defines a type and returns it, a map describing it that holds no key. `spec`:

  - `:name`, a qualified symbol, which also names the type's class;
  - `:fields`, each `{:key :sym :optional?}`;
  - `:checks`, each `{:id :waits :run}` and optionally `:concerns`, `:doc`, `:reads` (the keys it
    reads), `:sources` (the sources it reads, compared with `=` by `fetching`), `:fetches?`,
    `:shape-of` (the key of the field it is the shape check of) and `:gate` (a key: where it
    is absent, the check passes without running). `:run` is a compiled check of the engine.
    A check waits on the checks in its `:waits` and on the shape check of each key it reads,
    as [[waits-of]] says. The shape check of an optional field passes where its field is
    absent;
  - `:interfaces`, the interfaces every sealed value implements (a protocol's among them), and
    `:methods`, a map from each method's signature, as the proof strategy's definition takes
    it, to a fn of `current` and `refuse` that returns the method's function. That function
    takes the value first and calls `refuse` with it where `current`, a volatile, holds false.
    `toString` is given a `current` that always holds true;
  - optionally `:guard`, what [[guard-maker]]'s form evaluates to where the definition placed
    it; without one, the guards are made by the form placed here, which every such type
    shares; and optionally `:change`, what [[change-guard-maker]]'s form evaluates to, in the
    same way.

  `wiring` names the proof `:strategy` and the engine's `:define`, `:run-all` and `:runner`,
  which runs the checks that read no source on the calling thread. Defining a
  type under a name already defined is redefinition: the definition that the name's namespace
  maps the name to is displaced. Its values stay values of their class and are no longer
  proven: a write that changes one, and every method but `toString` called with one, throws
  the refusal `:recognitum/displaced`. [[draft]] of one gives a draft of the type's current
  definition. [[make]] with the displaced definition, and [[seal]] of a draft of its class,
  throw the refusal `:recognitum/displaced-constructor`, so a constructor or a class held from
  before makes nothing."
  [spec {:keys [strategy define run-all runner]}]
  (let [displaced (named-now (:name spec))
        current (volatile! true)
        unsealed? (true? (:unsealed spec))
        h (proof/define-type strategy (:name spec)
            (cond-> {:keys (mapv :key (:fields spec))
                     :interfaces (vec (:interfaces spec))
                     :methods (let [refuse (fn [v] (throw (if unsealed?
                                                            (displaced-unsealed (:name spec) v)
                                                            (displaced-refusal (:name spec) v))))]
                                (into {} (for [[[n ps :as sig] make] (:methods spec)]
                                           [sig (if (and (= "toString" n) (empty? ps))
                                                  (make (volatile! true) refuse)
                                                  (make current refuse))])))}
              unsealed? (assoc :unsealed true)))
        [vc dc] (proof/classes h)
        type (let [t (compile-type spec strategy define run-all runner)]
               ;; an unsealed type's memories never show every check passing through a value of
               ;; its class: its `Hot` names Void, of which nothing is an instance
               (assoc t ::class vc ::draft-class dc ::gate (volatile! nil) ::unsealed unsealed?
                      ::hot (hot-of (if unsealed? Void vc) dc strategy (:ids t) (:readers t) (::readers-v t))))
        ids (:ids type)
        ^Hot hot (::hot type)
        masks? (some? (.-bits hot))
        all-mask (.-all hot)
        nothing (Memo. type nil #{} #{} nil (when masks? 0))
        memo (fn [data ids]
               (if (empty? ids)
                 nothing
                 (let [m (proof/open h)
                       mask (mask-of hot ids)]
                   (proof/mark! h m (PassKey. data ids mask))
                   (Memo. type data ids #{} m mask))))
        ;; [[memo]] of the checks of `mask`, for a type with masks
        memo-m (fn [data ^long mask]
                 (if (zero? mask)
                   nothing
                   (let [m (proof/open h)
                         ids (set-of hot mask)]
                     (proof/mark! h m (PassKey. data ids mask))
                     (Memo. type data ids #{} m mask))))
        bits (.-bits hot)
        ;; the mask of the ids in `xs`, a collection, and of the keys of `m`, a map
        bits-of (fn ^long [xs] (reduce (fn [^long a id] (bit-or a (long (bits id)))) 0 xs))
        key-bits-of (fn ^long [m] (reduce-kv (fn [^long a id _] (bit-or a (long (bits id)))) 0 m))
        engine (:engine type)
        run* (::run type)
        declared (:keys type)
        declared? (member-of declared)
        required-v (::required-v type)
        required (:required type)
        ;; whether `data` lacks a required field
        lacks? (fn [data] (not (reduce (fn [_ k] (if (contains? data k) true (reduced false))) true required-v)))
        readers (:readers type)
        readers-v (::readers-v type)
        removed (proof/removed strategy)
        ;; whether a run's result has nothing failed or blocked: first by identity with a result
        ;; already found clean, as results are immutable
        clean (volatile! nil)
        clean? (fn [result]
                 (or (identical? result (.deref ^clojure.lang.Volatile clean))
                     (when-not (or (seq (:failed result)) (seq (:blocked result)))
                       (vreset! clean result)
                       true)))
        ;; throws the failure of `result`, the run of the checks on `data`, where a check failed
        ;; or, where `may-lack?`, a required field is absent
        refuse! (fn [data result may-lack?]
                  (let [absent (when may-lack? (missing type data))]
                    (when (or absent (not (clean? result)))
                      (throw (check-failed type (when-not (clean? result) (report type result)) absent)))))
        ;; `result`, the run of the checks on `data`, sealed
        seal! (fn [data result may-lack?]
                (if (and (clean? result) (not (and may-lack? (lacks? data))))
                  (proof/seal h data)
                  (do (refuse! data result may-lack?)
                      (proof/seal h data))))
        ;; each declared key whose readers read no source, to a run of those readers alone
        run-of (into {} (for [k declared
                              :let [rs (get readers k #{})]
                              :when (not-any? #(:fetches? ((:by-id type) %)) rs)]
                          [k (runner engine rs)]))
        own! (fn [old]
               (when-not (instance? vc old)
                 (throw (ex-info (str "a write starts from a value of " (:name type))
                                 {:error :recognitum/not-a-value :type (:name type)})))
               (when-not (.deref ^clojure.lang.Volatile current)
                 (throw (displaced-refusal (:name type) old))))
        own-memo (fn [d]
                   (let [m (when (draft? d) (marks-of d))]
                     (when-not (and (instance? Memo m) (identical? type (.-type ^Memo m)))
                       (throw (ex-info (str "not a draft of " (:name type) ": " (pr-str d))
                                       {:error :recognitum/not-a-draft :type (:name type)})))
                     m))
        own-draft (fn [d]
                    (let [m (own-memo d)]
                      [(.-data ^Draft d) (passes type (.-data ^Draft d) m) m]))
        ;; the memory cell of `v`, a value of this unsealed type's current definition
        own-value (fn [v]
                    (when-not (instance? vc v)
                      (throw (ex-info (str "not a value of " (:name type) ": " (pr-str v))
                                      {:error :recognitum/not-a-value :type (:name type)})))
                    (when-not (.deref ^clojure.lang.Volatile current)
                      (throw (displaced-unsealed (:name type) v)))
                    (proof/memory strategy v))
        ;; what a run reads of `x`, a draft or a value of this unsealed type: its entries, what
        ;; it passes, its memory, and the cell that holds the memory
        own-subject (fn [x]
                      (if unsealed?
                        (let [cell (own-value x)
                              m @cell]
                          [x (passes type x m) m cell])
                        (let [m (own-memo x)
                              data (.-data ^Draft x)]
                          [data (passes type data m) m (.-cell ^Draft x)])))
        ;; a draft's entries, what it passes, its memory, and whether it passes every check:
        ;; through the mask where the type has one
        ;; each mask of passing checks asked for, to a run of the checks it leaves: the runner
        ;; over those checks where none reads a source, else every check but the known
        runs (java.util.concurrent.ConcurrentHashMap.)
        fetching-m (when masks? (mask-of hot (filter #(:fetches? ((:by-id type) %)) ids)))
        ;; past 1000 masks, a mask not kept runs every check but the known, building nothing
        run-known (fn [^long km known]
                    (or (.get runs km)
                        (if (and (< (.size runs) 1000) (zero? (bit-and-not (long fetching-m) km)))
                          (let [r (runner engine (set-of hot (bit-and-not all-mask km)))
                                f (fn [data] (r data nil))]
                            (.putIfAbsent runs km f)
                            f)
                          (fn [data] (run* data known)))))
        ;; a draft's entries, what it passes, its memory, whether it passes every check, and a
        ;; run of the checks left: through the mask where the type has one
        own-for-seal (fn [d]
                       (if masks?
                         (let [m (own-memo d)
                               data (.-data ^Draft d)
                               km (passes-mask type data m)]
                           (if (== km all-mask)
                             [data ids m true nil]
                             (let [known (set-of hot km)]
                               [data known m false (run-known km known)])))
                         (let [[data known m] (own-draft d)]
                           [data known m (empty? (minus ids known)) #(run* % known)])))
        ;; A run writes what it found over the memory it started from, less `forget`. Where
        ;; another run has written since, it only forgets what failed and `forget`: a pass it
        ;; found may predate a forget written since.
        remember! (fn remember!
                    ([cell data m0 known to-run result] (remember! cell data m0 known to-run result ()))
                    ([cell data m0 known to-run result forget]
                     (let [failed (keys (:failed result))]
                       (when-not (or (and (empty? to-run) (empty? forget))
                                     (compare-and-set! cell m0
                                                       (memo data (reduce disj
                                                                          (into (reduce disj known forget)
                                                                                (passed-in to-run result))
                                                                          failed))))
                         (swap! cell #(memo data (reduce disj (passes type data %) (concat failed forget))))))))
        ;; [[remember!]] for a type with masks, with nothing more to forget: `km` the mask of
        ;; the checks known to pass, `tm` of those run
        remember-m! (fn [^Draft d m0 km tm result]
                      (let [data (.-data d)
                            km (long km)
                            tm (long tm)
                            fm (key-bits-of (:failed result))
                            bm (bits-of (:blocked result))]
                        (when-not (compare-and-set! (.-cell d) m0
                                                    (memo-m data (bit-and-not (bit-or km (bit-and-not tm (bit-or fm bm))) fm)))
                          (swap! (.-cell d) #(memo-m data (bit-and-not (passes-mask type data %) fm))))))
        ;; each set of checks picked, to the closure of its checks of this type, as a set and
        ;; as a mask or nil. Past 1000, a set not kept is closed anew.
        closures (java.util.concurrent.ConcurrentHashMap.)
        closure-of (fn [picked]
                     (or (.get closures picked)
                         (let [closed (select/closure type (set/intersection ids (set picked)))
                               c [closed (mask-of hot closed)]]
                           (when (< (.size closures) 1000) (.putIfAbsent closures picked c))
                           c)))
        ;; the checks of `picked` that read a source
        fetching-in (fn [picked] (filter #(:fetches? ((:by-id type) %)) picked))
        ;; `groups`, each `[picked xs is kind]`: the checks a selection picks in a type, a vector
        ;; of values, the indices in `xs` of the drafts of the type, or of its values where it is
        ;; unsealed, ascending, and the kind of run: nil for check's, `:recheck` for recheck's,
        ;; `:seal` for seal's (check's, with the floor of each value). This type's group comes
        ;; first; each other type's gate takes its own. Each draft or value is read once, and
        ;; runs where it has anything to run.
        check-group (fn [groups entries]
                      (let [[[picked xs is kind] & more] groups
                            [closed closed-m] (closure-of picked)
                            named (when (= kind :recheck) (set/intersection ids (set picked)))
                            forget (when named (fetching-in named))
                            entries (into entries
                                          (if (and masks? (nil? kind) (not unsealed?))
                                            (let [closed-m (long closed-m)]
                                              (keep (fn [i]
                                                      (let [d (xs i)
                                                            m0 (own-memo d)
                                                            data (.-data ^Draft d)
                                                            km (passes-mask type data m0)
                                                            tm (bit-and-not closed-m km)]
                                                        (when-not (zero? tm)
                                                          {:i i
                                                           :type type
                                                           :to-run (set-of hot tm)
                                                           :job [engine data (set-of hot (bit-and-not (long all-mask) tm))]
                                                           :done #(remember-m! d m0 km tm %)})))))
                                            (keep (fn [i]
                                                    (let [[data known m0 cell] (own-subject (xs i))
                                                          to-run (case kind
                                                                   nil      (minus closed known)
                                                                   :recheck (into named (minus closed known))
                                                                   :seal    (minus (select/closure type (into closed (select/floor type data)))
                                                                                   known))]
                                                      (when (seq to-run)
                                                        {:i i
                                                         :type type
                                                         :to-run to-run
                                                         :job [engine data (set/difference ids to-run)]
                                                         :done #(remember! cell data m0 known to-run % forget)})))))
                                          is)]
                        (if-let [[[_ xs [i]]] (seq more)]
                          ((gate (type-of! (xs i))) ::check-all (vec more) entries)
                          (run-jobs (:run-all type) (in-group-order entries)))))
        run-draft (fn [to-run [data known m0 cell] forget]
                    (let [result (run type data (set/difference ids to-run))]
                      (remember! cell data m0 known to-run result forget)
                      result))
        ;; each key whose readers read no source, to its guard: an assoc of the key runs those
        ;; readers on the old value with the key set, and throws what the change would throw
        guards (let [make (or (:guard spec) (guard-maker With))
                     refuse (fn [old result]
                              (throw (if result
                                       (check-failed type (report type result))
                                       (displaced-refusal (:name type) old))))]
                 (into {} (for [[k r] run-of] [k (make current r k clean? refuse)])))
        ;; each declared key, to its guard, or to `none` where its readers read a source
        key-guards (let [m (java.util.IdentityHashMap.)]
                     (doseq [k declared] (.put m k (get guards k none)))
                     m)
        readers-m (.-readers-m hot)
        ;; for a type without masks: each declared key, to a bit of a long, where it declares at
        ;; most 64; and each set of keys a change of several keys changes, where no check of
        ;; theirs reads a source, as those bits or else as the set of the checks that read them,
        ;; to a runner of those checks. Past 1000, a set not kept is built anew.
        key-bits (when (and (not masks?) (<= (count declared) 64))
                   (let [m (java.util.IdentityHashMap.)]
                     (doseq [[i k] (map-indexed vector (sort-by str declared))] (.put m k (bit-shift-left 1 i)))
                     m))
        change-runs (java.util.concurrent.ConcurrentHashMap.)
        run-checks (fn [cache-key changes]
                     (or (.get change-runs cache-key)
                         (let [r (runner engine (reduce (fn [a k] (into a (readers-v k []))) #{} (keys changes)))]
                           (when (< (.size change-runs) 1000) (.putIfAbsent change-runs cache-key r))
                           r)))
        ;; a change of a key whose readers read a source: every check that reads a key changed, on
        ;; the view of old with the changes applied
        whole-change (fn [old changes may-lack?]
                       (let [view (Changed. old changes removed)]
                         (refuse! view
                                  (run* view (if masks?
                                               (set-of hot (bit-and-not (long all-mask)
                                                                        (long (reduce-kv (fn [m k _] (bit-or (long m) (long (readers-m k 0)))) 0 changes))))
                                               (reduce (fn [a k] (reduce disj a (readers-v k [])))
                                                       ids (keys changes))))
                                  may-lack?)))
        ;; a change of several keys, or a removal: the readers of the keys changed run on the
        ;; view of old with the changes applied, and nothing else
        change-many (fn [old ^clojure.lang.IPersistentMap changes]
                      (let [view (Changed. old changes removed)
                            it (.iterator ^Iterable changes)]
                        (loop [mask 0, to-run #{}, may-lack? false, sourced? false]
                          ;; `mask` the bits of the readers of the keys changed, with masks; else
                          ;; of the keys changed, with key bits; else `to-run` those readers
                          (if (.hasNext it)
                            (let [^java.util.Map$Entry e (.next it)
                                  k (.getKey e)
                                  held (not (identical? (.getValue e) removed))
                                  g (.get key-guards k)]
                              (when (and held (nil? g)) (refuse-undeclared! type (keys changes) view))
                              (recur (cond masks?   (bit-or mask (long (readers-m k 0)))
                                           key-bits (bit-or mask (long (or (.get ^java.util.IdentityHashMap key-bits k) 0)))
                                           :else    mask)
                                     (if (or masks? key-bits) to-run (into to-run (readers-v k [])))
                                     (or may-lack? (and (not held) (contains? required k)))
                                     (or sourced? (identical? g none))))
                            (if sourced?
                              (whole-change old changes may-lack?)
                              (refuse! view
                                       (cond masks?
                                             (if (zero? mask)
                                               engine-passed
                                               (let [km (bit-and-not (long all-mask) mask)]
                                                 ((run-known km (set-of hot km)) view)))
                                             key-bits
                                             ((run-checks mask changes) view nil)
                                             (seq to-run)
                                             ((run-checks to-run changes) view nil)
                                             :else engine-passed)
                                       may-lack?))))))
        ;; the change guard, `(cg old changes)`: a change that sets one key goes to that key's guard
        change-guard ((or (:change spec) (change-guard-maker)) own! key-guards removed none change-many whole-change)
        ;; `(write old entries)`, which only `installed` calls: the change guard of what
        ;; `entries` changes, then `entries` sealed
        write (fn [old entries]
                (own! old)
                (let [changed (changed-keys old entries)]
                  (if (empty? changed)
                    old
                    (do (change-guard old (into {} (map (fn [k] [k (get entries k removed)])) changed))
                        (proof/seal h (with-meta-of entries old))))))
        ;; the seal of `v`, a value of this unsealed type, against the checks `picked`: runs them,
        ;; what they wait on and the floor, less what `v` passes, and returns `v` or throws
        seal-value (fn [v picked]
                     (let [[data known m0 cell] (own-subject v)
                           to-run (minus (select/closure type (into (set/intersection ids (set picked))
                                                                    (select/floor type data)))
                                         known)
                           result (when (seq to-run) (run type data (set/difference ids to-run)))]
                       (when result (remember! cell data m0 known to-run result))
                       (refuse! data (or result engine-passed) true)
                       v))
        ;; the installed write. Its three-argument arity, which the class's channel reaches, serves
        ;; both kinds of type; an unsealed type's strategy calls no other arity.
        write-all (fn
                    ([old entries] (write old entries))
                    ;; the change guard takes every change of one key, so this arity is never called
                    ([old entries _ _] (write old entries))
                    ([op x y]
                     (case op
                       ::make (let [data (proof/plain-map x)]
                                (when-not (.deref ^clojure.lang.Volatile current)
                                  (throw (displaced-constructor (:name type) y)))
                                (when-not (all-declared? declared? data) (refuse-undeclared! type (keys data)))
                                (if unsealed?
                                  (proof/build h data (atom nothing))
                                  (seal! data (run* data #{}) true)))
                       ::open (if unsealed?
                                (throw (no-drafts (:name type)))
                                (Draft. {} (atom nothing) nil))
                       ::draft-of (cond unsealed? (throw (no-drafts (:name type)))
                                        (instance? vc x) (Draft. (proof/plain-map x) (atom (Memo. type x ids #{} x all-mask)) (meta x))
                                        :else (throw (ex-info (str "not a value of " (:name type)) {:error :recognitum/not-a-value})))
                       ::rewrite (let [[data] (own-draft x)
                                       y (proof/plain-map y)
                                       changed (changed-keys data y)]
                                   (if (empty? changed)
                                     x
                                     (rewritten x y #(into % changed))))
                       ::clean (let [_ (when unsealed? (throw (no-drafts (:name type))))
                                     [data] (own-draft x)
                                     kept (select-keys data (:keys type))]
                                 (if (= (count kept) (count data))
                                   x
                                   (rewritten x kept #(into % (remove (:keys type)) (keys data)))))
                       ::seal (if unsealed?
                                (seal-value x y)
                                (let [[data known m0 all-pass? run-left] (own-for-seal x)]
                                  (when-not (.deref ^clojure.lang.Volatile current)
                                    (throw (displaced-draft (:name type))))
                                  (when-not (all-declared? declared? data) (refuse-undeclared! type (keys data)))
                           ;; a draft that passes every check runs none
                                  (let [result (when-not all-pass? (run-left data))
                                        rep (when-not (or all-pass? (clean? result)) (report type result))]
                                    (if (or rep (lacks? data))
                                      (do (remember! (.-cell ^Draft x) data m0 known (minus ids known) result)
                                          (throw (check-failed type rep (missing type data))))
                               ;; every check passes: the value sealed is the draft's proof. Where
                               ;; another run has written since, there is nothing failed to forget.
                                      (let [v (proof/seal h (with-meta-of data x))]
                                        (when-not all-pass?
                                          (compare-and-set! (.-cell ^Draft x) m0 (Memo. type v ids #{} v all-mask)))
                                        v)))))
                       ::check (let [[_ known :as own] (own-subject x)
                                     named (set/intersection ids (set y))]
                                 (run-draft (minus (select/closure type named) known) own ()))
                       ::check-all (check-group x y)
                       ::type type
                       ::current? @current
                ;; whether `x` is a value sealed under this definition, which is current
                       ::sealed? (and (.deref ^clojure.lang.Volatile current) (proof/proven? h x))
                       ::displace (do (vreset! current false) nil)
                       ::recheck (let [[_ known :as own] (own-subject x)
                                       named (set/intersection ids (set y))]
                            ;; a named check that reads a source is forgotten, then remembered only if this run passes it
                                   (run-draft (into named (set/difference (select/closure type named) known)) own
                                              (fetching-in named))))))]
    (if unsealed?
      ;; each change of a value carries its memory: the new value remembers what the old one
      ;; remembered, and the keys the change writes
      (proof/install-carry!
       h
       write-all
       (fn [old changes]
         (let [cell (own-value old)]
           (refuse-undeclared! type (keys changes))
           (let [mo @cell]
             (atom (if (and (instance? Memo mo) (some? (.-proof ^Memo mo)))
                     (let [^Memo mo mo]
                       (Memo. (.-type mo) (.-base mo) (.-passes mo) (into (.-written mo) (keys changes))
                              (.-proof mo) (.-mask mo)))
                     mo))))))
      (proof/install-write!
       h
       write-all
       (fn [k] (get guards k))
       change-guard))
    (vreset! (::gate type) (proof/installed strategy vc))
    (when displaced
      ((gate displaced) ::displace nil nil))
    type))

;;; ------------------------------------------------------------------ values

(defn value-class
  "The class of `type`'s sealed values."
  [type]
  (::class type))

(defn make
  "A sealed value of `type` holding the entries of map `m`, after every check passes. Throws
  where `m` holds a key the type does not declare, where a check fails or a required field is
  missing, or where a later definition has displaced `type`; the ex-data's `:error` is
  `:recognitum/undeclared-keys`, `:recognitum/check-failed` (which names the failed checks
  under `:failed` and the absent required fields under `:missing`, where there are any) or
  `:recognitum/displaced-constructor`. `remedy`, a string, is the displaced refusal's advice
  in place of a call to the current `map->T`."
  ([type m] (make type m nil))
  ([type m remedy] ((gate type) ::make m remedy)))

(defn sealed?
  "Whether `x` is a sealed value of the current definition of its type: as the type's proof
  strategy answers, so never a value of an unsealed type."
  [x]
  (let [t (type-of x)]
    (boolean (and t (not (draft? x)) (not (class? x)) ((gate t) ::sealed? x nil)))))

(defn unsealed?
  "Whether `type` was defined unsealed: its values are made without checks and carry what
  passed."
  [type]
  (true? (::unsealed type)))

(defn- held-memory
  "What `v`, a value of the unsealed `type`, remembers, or nil where `type` is displaced or
  `v` holds no memory."
  [type v]
  (when (current? type)
    (some-> (proof/memory (:strategy type) v) deref)))

(defn draft
  "A draft: of a type (given its class), holding nothing and passing nothing; of a sealed
  value, holding its entries and passing every check; of a value of a displaced definition, a
  draft of the type's current definition holding its entries and passing nothing, or, where
  the type's name no longer names a current definition of the type, a refusal saying the type
  has no current definition; of a draft, that draft itself, sharing what it remembers. An
  unsealed type has no drafts: refuses its class and its values."
  [x]
  (cond (draft? x) x
        (class? x) ((gate (type-of! x)) ::open nil nil)
        :else      (let [t (value-type! x)]
                     ;; a current unsealed type's gate refuses ::draft-of itself
                     (if (current? t)
                       ((gate t) ::draft-of x nil)
                       (let [_   (when (unsealed? t) (throw (no-drafts (:name t))))
                             now (named-now (:name t))]
                         (when-not (and now (current? now)) (throw (no-definition (:name t) x)))
                         (with-meta ((gate now) ::rewrite ((gate now) ::open nil nil) (proof/plain-map x))
                           (meta x)))))))

(defn- orphan?
  "Whether `x` is a value of a displaced definition whose name no longer names a current
  definition of its type, so that [[draft]] of it refuses."
  [x]
  (and (not (draft? x))
       (let [t (type-of x)]
         (and (some? t) (not (current? t))
              (let [now (named-now (:name t))]
                (not (and now (current? now))))))))

(defn clean
  "`d` without the keys its type does not declare, remembering what `d` remembers."
  [d]
  ((gate (value-type! d)) ::clean d nil))

(defn- not-sealable [d]
  (ex-info (str "not a draft, a sealed value or a value of an unsealed type: " (pr-str d))
           {:error :recognitum/not-a-draft :value d}))

(defn seal
  "The sealed value of draft `d`, after every check it does not remember as passing passes.
  Refuses a draft holding an undeclared key before any check runs. Otherwise `d` remembers
  each check that passed and forgets each that failed, whether or not the seal succeeds.
  Throws as [[make]] does; a draft of a displaced definition's class is refused before any
  check runs. A sealed value is returned as it is.

  With `sel`, a draft seals against every check: `sel` is [[recognitum.select/every]], or the
  seal throws, running nothing. A value of an unsealed type runs the checks `sel` selects,
  what they wait on and the shape checks of the fields it must or does hold, less what it
  passes; it remembers what passed and forgets what failed, and is returned itself, or the
  seal throws as [[make]] does. Without `sel`, it is sealed against every check."
  ([d]
   (cond (draft? d)  ((gate (type-of! d)) ::seal d nil)
         (sealed? d) d
         :else (let [t (type-of d)]
                 (some->> t (refuse-type! d))
                 (if (and t (unsealed? t))
                   ((gate t) ::seal d (:ids t))
                   (throw (not-sealable d))))))
  ([d sel]
   (cond (draft? d)  (if (= select/every sel)
                       (seal d)
                       (throw (ex-info (str "a draft seals against every check, so seal takes no selection"
                                            " but rec/every for one: " (pr-str sel))
                                       {:error :recognitum/draft-selection :selection sel})))
         (sealed? d) d
         :else (let [t (type-of d)]
                 (some->> t (refuse-type! d))
                 (if (and t (unsealed? t))
                   ((gate t) ::seal d (select/select t sel))
                   (throw (not-sealable d)))))))

(defn- passes-of
  "The checks `x` passes, as far as anything shows: every check for a sealed value, what a draft
  remembers."
  [type x]
  (cond (draft? x) (passes type (.-data ^Draft x) (marks-of x))
        (sealed? x) (:ids type)
        (unsealed? type) (passes type x (held-memory type x))
        :else #{}))

(defn- data-of [x] (if (draft? x) (.-data ^Draft x) x))

(defn- answer
  "What a run of `sel` answers: true, or the report of `result`, with the required fields
  `absent` under `:missing` where any is."
  ([type result sel picked to-run] (answer type result sel picked to-run nil))
  ([type result sel picked to-run absent]
   (let [r (report type result #(pulled-back type sel picked to-run %))]
     (cond absent (assoc (or r engine-passed) :missing absent)
           r      r
           :else  true))))

(defn- presence
  "The presence check of the required field `f`: a check with no name, standing for itself."
  [f]
  [::present f])

(defn- selected
  "The checks of `type` that `sel` selects, the presence checks of its required fields among
  them. A presence check has no name, is a shape check of its field, reads no source and reads
  its field alone, so a selection selects it as it would any check of that kind."
  [type sel]
  (let [required (:required type)
        op (when (map? sel) (::select/op sel))]
    (case op
      (:every :shape :pure) (into (select/select type sel) (map presence) required)
      :reading (cond-> (select/select type sel) (contains? required (:key sel)) (conj (presence (:key sel))))
      :union (into #{} (mapcat #(selected type %)) (:xs sel))
      :except (reduce set/difference (selected type (:s sel)) (map #(selected type %) (:xs sel)))
      (select/select type sel))))

(defn- asked*
  "The required fields of `type` whose presence `sel` asks: those whose presence check `sel`
  selects, or something it selects waits on. Every check waits on the presence checks of the
  required fields it reads."
  [type sel]
  (let [required (:required type)
        s (selected type sel)]
    (into (into #{} (keep #(when (vector? %) (second %))) s)
          (comp (mapcat #(get-in type [:by-id % :reads])) (filter required))
          (select/closure type (remove vector? s)))))

(defn- asked
  "[[asked*]] as a vector, kept per type and selection where the type has kept fewer than a
  thousand."
  [type sel]
  (if (= select/every sel)
    (::required-v type)
    (let [^java.util.concurrent.ConcurrentHashMap kept (::asked type)]
      (or (.get kept sel)
          (let [a (vec (sort-by str (asked* type sel)))]
            (when (< (.size kept) 1000) (.putIfAbsent kept sel a))
            a)))))

(defn- absent-of
  "The fields of `ask`, a vector, that `data` does not hold, or nil where it holds each."
  [ask data]
  (let [^clojure.lang.IPersistentVector ask ask
        n (.count ask)]
    (loop [i 0]
      (cond (== i n) nil
            (contains? data (.nth ask i)) (recur (inc i))
            :else (into #{} (remove #(contains? data %)) ask)))))

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
  removed a check that a wait then ran. Where `sel` is every check, the report holds under
  `:missing` the required fields a draft lacks, and is a report even where every check
  passed."
  [x sel]
  (let [type (value-type! x)
        picked (select/select type sel)]
    (if (or (draft? x) (unsealed? type))
      (let [known (passes-of type x)
            to-run (set/difference (select/closure type picked) known)]
        (answer type ((gate type) ::check x picked) sel picked to-run (absent-in type x sel)))
      true)))

(defn recheck
  "Runs the checks `sel` names in `x` whether or not `x` passes them, and those they wait on that
  `x` does not pass. A draft remembers as [[check]] does; a sealed value is left as it is.
  Returns as [[check]] does."
  [x sel]
  (let [type (value-type! x)
        picked (select/select type sel)
        known (passes-of type x)
        to-run (into picked (set/difference (select/closure type picked) known))]
    (answer type
            (if (or (draft? x) (unsealed? type))
              ((gate type) ::recheck x picked)
              (run type x (set/difference (:ids type) to-run)))
            sel picked to-run (absent-in type x sel))))

(defn- run-batch
  "Runs, over every value in `xs`, what `plan` says for its type in one run of the engine, so
  values that read the same source, of one type or several, share its calls. `(plan type)` is
  `[sel kind]`: the selection, and the kind of run, nil for [[check]]'s, `:recheck` for
  [[recheck]]'s, or `:seal` for a seal's, which adds the floor of each value. Drafts and values
  of unsealed types remember as the single op would. Returns a vector with one answer per value,
  each true or a report as [[check]] returns."
  [xs plan]
  (let [xs (vec xs)
        n (count xs)
        ;; each type, to what its selection picks in it, the closure of that, its mask, the
        ;; selection and the kind of run: the same for every value of the type in one call
        per-type (java.util.IdentityHashMap.)
        types (mapv (fn [x]
                      (let [type (value-type! x)]
                        (when-not (.containsKey per-type type)
                          (let [[sel kind] (plan type)
                                picked (select/select type sel)
                                closed (select/closure type picked)]
                            (.put per-type type [picked closed (mask-of (::hot type) closed) sel kind
                                                 (when-not (= :seal kind) (not-empty (asked type sel)))])))
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
              (seq groups) ((gate (first order)) ::check-all groups others)
              (seq others) (run-jobs (:run-all (types (:i (first others)))) others)
              :else [])
        out (object-array n)
        ;; the required fields a value lacks, where its run reports them: a seal's run does not
        absent (fn [i] (let [type (types i)
                             x (xs i)]
                         (when-let [ask (nth (.get per-type type) 5)]
                           (when (or (draft? x) (unsealed? type))
                             (absent-of ask (data-of x))))))]
    (doseq [[i r to-run] ran]
      (let [type (types i)
            pt (.get per-type type)]
        (aset out i (answer type r (nth pt 3) (nth pt 0) to-run (absent i)))))
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

(defn proves?
  "Whether `x` holds every required field and passes every check `sel` names in it, every
  check those wait on, and the shape check of each field it must or does hold. Always true for
  a sealed value of a type's current definition; for a draft of a type's current definition,
  or a value of an unsealed type's current definition, a matter of its entries and what it
  remembers; false for anything else, a draft made before its type was defined again
  included, and a type, its class or the type itself."
  [x sel]
  (if-let [type (when-not (class? x) (type-of x))]
    (or (sealed? x)
        (and (or (draft? x) (and (unsealed? type) (instance? (::class type) x)))
             (current? type)
             (let [data (data-of x)]
               (and (nil? (missing type data))
                    (set/subset? (select/closure type (into (select/select type sel)
                                                            (select/floor type data)))
                                 (passes-of type x))))))
    false))

(defn proven-checks
  "The ids of the checks `x` passes: every check of its type for a sealed value, those a draft
  or a value of an unsealed type remembers."
  [x]
  (passes-of (value-type! x) x))

(defn proven-concerns
  "The ids of the concerns whose checks `x` passes, as [[proves?]] answers for each."
  [x]
  (let [type (value-type! x)]
    (set (for [t (distinct (mapcat :concerns (:checks type)))
               :when (proves? x t)]
           t))))

(defn checks-of
  "The ids of the checks `sel` names in the type of `x`: a value, a draft or a type's class."
  [sel x]
  (select/select (type-of! x) sel))

;;; ------------------------------------------------------------------ probing

(defn- probe-type!
  "The type whose class is `c`, a current definition; refuses anything else."
  [c]
  (let [t (when (class? c) (type-of-class c))]
    (when-not t
      (throw (ex-info (str "probe takes a type's class: " (pr-str c))
                      {:error :recognitum/not-a-type :value c})))
    (when-not (current? t)
      (throw (ex-info (str (:name t) " was redefined: this class is of an earlier definition. Probe the"
                           " class " (namespace (:name t)) " now names " (name (:name t)))
                      {:error :recognitum/displaced-constructor :type (:name t)})))
    t))

(defn- entries
  "The entries of map `m`, a draft, a value of any type or any other map, as a plain map; its
  memory, where it has one, is not read."
  [m]
  (cond (draft? m) (.-data ^Draft m)
        (map? m)   (proof/plain-map m)
        :else      (throw (ex-info (str "probe reads a map: " (pr-str m))
                                   {:error :recognitum/not-a-map :value m}))))

(defn probe-all
  "For each map of `field-maps`, what [[check]] with `sel` answers of a fresh draft of the type
  whose class is `c` holding its entries, with the keys the type does not declare under
  `:undeclared`: true, or a report. One run of the engine over every map, in which each read
  of a source that `overrides` maps calls its override in its place. Makes no draft and writes
  no memory."
  [c field-maps sel overrides]
  (let [type (probe-type! c)
        picked (select/select type sel)
        to-run (select/closure type picked)
        assumed (set/difference (:ids type) to-run)
        ask (asked type sel)
        datas (mapv entries field-maps)
        engine (:engine type)
        jobs (mapv (fn [d] [engine d assumed]) datas)
        o (not-empty overrides)
        results (if (and (nil? o) (nil? *overrides*))
                  ((:run-all type) jobs)
                  (binding [*overrides* o] ((:run-all type) jobs)))
        declared (:keys type)]
    (mapv (fn [d result]
            (let [r (answer type result sel picked to-run (absent-of ask d))
                  u (not-empty (into #{} (remove #(contains? declared %)) (keys d)))]
              (cond (nil? u)  r
                    (true? r) (assoc engine-passed :undeclared u)
                    :else     (assoc r :undeclared u))))
          datas (vec results))))

(defn probe
  "What [[probe-all]] answers of the one map `fields`."
  [c fields sel overrides]
  (nth (probe-all c [fields] sel overrides) 0))

;;; ------------------------------------------------------------------ many values at once

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

(defn- scanner
  "A function `(scan x at)` that adds to `found`, inner nodes first, each draft the walk
  reaches in `x`, and each value of an unsealed type where `enter?`, as `[at node height
  fields]`: `at` its path, last step first, and `fields` the keys of its fields in which a draft
  is reached. `at` is the path to `x`; a node in key position ends its path with `key-step`.
  The function returns what `x` reaches, as above."
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
                    (or (vector? x) (seq? x)) (loop [s (seq x), i 0, r -1]
                                                (if s
                                                  (recur (next s) (inc i) (reach r (in (first s) i at)))
                                                  r))
                    :else -1)))]
    scan))

(defn- rebuild
  "`x` as the walk makes it: maps rebuilt as `clojure.walk` rebuilds them, keys and values;
  vectors, lists and sets by element; a list a list, any other sequence a vector, each with its
  metadata; anything else as it is. Each draft and each value of a type it reaches is replaced
  by `(f it)`, and not entered."
  [x f]
  (let [go #(rebuild % f)]
    (cond (not (coll? x)) x
          (or (draft? x) (value? x)) (f x)
          (map-entry? x) (clojure.lang.MapEntry/create (go (key x)) (go (val x)))
          (instance? clojure.lang.IRecord x) (reduce (fn [r [k v]] (conj r [(go k) (go v)])) x x)
          (map? x) (into (empty x) (map (fn [[k v]] [(go k) (go v)])) x)
          (vector? x) (into (empty x) (map go) x)
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
  have checks to run. Returns `[value nil]` or `[nil ex-data]` for each, in order."
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
        ;; definition. A value of an unsealed type holds no undeclared key.
        refused (mapv (fn [d] (let [t (type-of d)
                                    declared? (when t (declared?* t))]
                                (if (draft? d)
                                  (not (and declared? (all-declared? declared? (.-data ^Draft d))))
                                  (not declared?))))
                      ds)
        every-plan [select/every nil]
        value-plan [sel :seal]
        answers (run-batch (if (some true? refused)
                             (vec (keep-indexed (fn [i d] (when-not (refused i) d)) ds))
                             ds)
                           (fn [t] (if (unsealed? t) value-plan every-plan)))]
    (loop [i 0, j 0, out (transient [])]
      (if (== i (count ds))
        (persistent! out)
        (let [d (ds i)]
          (if (refused i)
            (recur (inc i) j (conj! out (cond (draft? d) (seal-or-refusal d sel)
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
            level (mapv (fn [[at d n fields :as e]]
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
