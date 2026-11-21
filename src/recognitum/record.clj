(ns recognitum.record
  "The record layer: types whose values read as maps and are proven to have passed their
  checks, drafts that remember which checks pass, checked writes, optional fields and closed
  types.

  [[define-type]] defines a type from compiled checks, a proof strategy and a check engine,
  which it receives as arguments, so that this layer names no strategy and no engine. It
  compiles the spec into the type map, asks the strategy for the type's classes and its
  handle, builds the type's installed write and guards from what the children of this
  namespace provide (`recognitum.record.memory` and `.draft` for what passes, `.views` for
  what a write's checks read, `.runs` for running checks, `.reports` for refusals), installs
  them, and displaces the definition it succeeds. The functions that act on values of any
  type are in `recognitum.record.values`, `.runs`, `.probe`, `.types` and `.walk`.

  Terms:

  - the **type map**, or the type: the map that [[define-type]] returns, which every function
    of the layer takes or finds from a value, a draft or a class;
  - the **installed write**: the function that [[define-type]] installs on the type's handle,
    which [[recognitum.record.types/gate]] answers. Its three-argument arity takes an
    operation keyword, and each operation, such as making a value or sealing a draft, is one
    **arm**;
  - the **readers** of a key: the checks that read it;
  - the **guards**: a key guard for each key whose readers read no source, which an `assoc`
    of that key calls, and the change guard, which every other change calls;
  - **masks**: in a type of at most 64 checks, each check has a bit of a `long`, and a set of
    checks is also kept as the `long` of their bits;
  - a **displaced** definition: one that a later definition of the same name replaced.

  The access key, which seals a type's values, never leaves the closures that [[define-type]]
  makes. Code outside reaches it only by calling the installed write, a key guard or the
  change guard, and each of these produces a sealed value only after the checks it runs
  pass."
  (:require
   [clojure.set :as set]
   [recognitum.proof :as proof]
   [recognitum.record.draft :refer [changed-keys draft? marks-of odd-after rewritten]]
   [recognitum.record.memory :refer [hot-of mask-of passes passes-mask set-of]]
   [recognitum.record.reports :refer [all-declared? check-failed displaced-constructor displaced-draft
                                      displaced-refusal displaced-unsealed engine-passed member-of missing no-drafts
                                      refuse-undeclared! report]]
   [recognitum.record.probe :refer [run-all-plain]]
   [recognitum.record.runs :refer [minus run run-jobs]]
   [recognitum.record.types :refer [gate type-of!]]
   [recognitum.record.values :refer [with-meta-of]]
   [recognitum.record.views :refer [change-guard-maker guard-maker view-type]]
   [recognitum.select :as select])
  (:import
   [recognitum.record.draft Draft]
   [recognitum.record.memory Hot Memo PassKey]
   [recognitum.record.views Changed]))

;;; ------------------------------------------------------------------ definitions

(def ^:private none (Object.))

(defonce ^:private definitions
  ;; each type name, to a weak reference to its latest definition, which the next definition of
  ;; the name displaces. Weak, because the values, drafts, constructors and class of a
  ;; definition all reach its type map: once nothing holds the type map, nothing is left to
  ;; displace, and it is collected with its class.
  (java.util.concurrent.ConcurrentHashMap.))

(defonce ^:private cleared
  ;; the references of `definitions` whose definition was collected
  (java.lang.ref.ReferenceQueue.))

(defn- succeed!
  "Records `type` as the latest definition of type name `n`, and returns the definition it
  replaces there, or nil; the caller displaces that one. The replacement is atomic: of two
  definitions of `n` made at once, each replaces a different one, and the one recorded last
  stays."
  [n type]
  (loop []
    (when-let [r (.poll ^java.lang.ref.ReferenceQueue cleared)]
      (.remove ^java.util.concurrent.ConcurrentHashMap definitions @r r)
      (recur)))
  (some-> ^java.lang.ref.WeakReference
   (.put ^java.util.concurrent.ConcurrentHashMap definitions n
         (proxy [java.lang.ref.WeakReference clojure.lang.IDeref] [type cleared]
           (deref [] n)))
          .get))

(defn- passed-in
  "The checks of `to-run` that passed in `result`."
  [to-run {:keys [failed blocked]}]
  (reduce disj (set/difference to-run blocked) (keys failed)))

(defn bound-check
  "The compiled check that runs `run`, a bundle's compiled check, in a type. `inputs` maps each
  input key that `run` reads to its input clause, a function of the value. The check calls
  each clause on the value, then calls `run` with the map from each input key to its clause's
  answer. An input whose clause reads an absent field is left out of that map, so `run` reads
  it as absent."
  [run inputs]
  (fn [value]
    (run (reduce-kv (fn [m k f]
                      (let [x (try (f value)
                                   (catch clojure.lang.ExceptionInfo e
                                     (if (contains? (ex-data e) :recognitum.checks/absent) ::absent (throw e))))]
                        (if (= ::absent x) m (assoc m k x))))
                    {} inputs))))

(defn- present-only
  "A compiled check that runs `run` where the value holds `k`, and passes without running
  where the value lacks `k`."
  [k run]
  (fn [value] (if (contains? value k) (run value) true)))

;;; ------------------------------------------------------------------ one-key writes

;; The view class of the key guards of every type whose spec gives no `:guard`.
(view-type With)

;;; ------------------------------------------------------------------ definition

(defn- in-group-order
  "`entries` in the order a group's run takes them. Where the entries that have a `:type` all
  have the same one, `entries` as they stand. Else the entries with no `:type` first, as they
  stand, then the others grouped by `:type`, each group ordered by `:i`, and the groups in the
  order of the map that `group-by` returns."
  [entries]
  (let [typed (filterv :type entries)]
    (if (every? #(identical? (:type (first typed)) (:type %)) typed)
      entries
      (into (filterv (complement :type) entries)
            (mapcat identity)
            (vals (group-by :type (sort-by :i typed)))))))

(defn waits-of
  "A map from the id of each check of `checks` (each `{:id :waits :reads :shape-of}`) to the
  set of every check it waits on: those its `:waits` names, and the shape check of each key it
  `:reads`, other than itself."
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
     ;; each selection, to whether it selects nothing in the type
     ::nothing (java.util.concurrent.ConcurrentHashMap.)
     :checks   (mapv #(dissoc % :run) checks)
     :by-id    (update-vals by-id #(dissoc % :run))
     :ids      (set (keys by-id))
     :readers  (apply merge-with into {} (for [c checks, k (:reads c)] {k #{(:id c)}}))
     ;; each key, to the ids of its readers, as a vector, which reduces without a seq
     ::readers-v (apply merge-with into {} (for [c checks, k (:reads c)] {k [(:id c)]}))
     :strategy strategy
     :run-all  run-all
     :engine   engine
     ;; `(run data assumed)`: the result of every check but those in `assumed`, on the calling
     ;; thread through `pure` where every check that reads a source is in `assumed`
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
  "The refusal `strategy` would make of a type whose values implement `interfaces` with methods
  of `signatures`, as [[define-type]] takes them, or nil where it would define the type. Takes
  the signatures alone, so that a macro can ask before the methods' functions exist. A
  refusal is a map with `:kind`, `:message`, and, by kind, `:method` (`[name arity]`, the name
  a symbol spelled as the signature spells it) or `:interfaces`."
  [strategy interfaces signatures]
  (proof/refusal strategy {:interfaces (vec interfaces)
                           :methods (into {} (map (fn [sig] [sig (fn [& _])])) signatures)}))

(defn- make-run-known
  "The `(run-known km known)` of a type with masks. `km` is the mask of the checks known to
  pass, and `known` the same checks as a set. Returns a function of a map that runs every
  check outside `known` on it and returns the result. Where no check outside `known` reads a
  source, that function is a runner's, kept in `runs` under `km` while `runs` has room; else it
  calls `run*`."
  [{:keys [fetching-m runner engine hot all-mask run*]} ^java.util.concurrent.ConcurrentHashMap runs]
  (fn [^long km known]
    (or (.get runs km)
        (if (and (< (.size runs) 1000) (zero? (bit-and-not (long fetching-m) km)))
          (let [r (runner engine (set-of hot (bit-and-not all-mask km)))
                f (fn [data] (r data nil))]
            (.putIfAbsent runs km f)
            f)
          (fn [data] (run* data known))))))

(defn- make-clean?
  "The `(clean? result)` of a type: whether a run's result has nothing failed and nothing
  blocked. `clean`, a volatile, holds the result last found clean, and a result identical to
  it answers true at once."
  [clean]
  (fn [result]
    (or (identical? result (.deref ^clojure.lang.Volatile clean))
        (when-not (or (seq (:failed result)) (seq (:blocked result)))
          (vreset! clean result)
          true))))

(defn- make-lacks?
  "The `(lacks? data)` of a type: whether `data` lacks one of the required fields
  `required-v`."
  [{:keys [required-v]}]
  (fn [data] (not (reduce (fn [_ k] (if (contains? data k) true (reduced false))) true required-v))))

(defn- make-refuse!
  "The `(refuse! data result may-lack?)` of `type`: throws the `:recognitum/check-failed`
  failure of `result`, the run of the checks on `data`, where a check failed or, where
  `may-lack?`, a required field is absent. Returns nil otherwise."
  [type clean?]
  (fn [data result may-lack?]
    (let [absent (when may-lack? (missing type data))]
      (when (or absent (not (clean? result)))
        (throw (check-failed type (when-not (clean? result) (report type result)) absent))))))

(defn- make-own!
  "The `(own! old)` of `type`: throws `:recognitum/not-a-value` where `old` is not a value of
  the class `vc`, and `:recognitum/displaced` where `current`, a volatile, holds false."
  [{:keys [vc type current]}]
  (fn [old]
    (when-not (instance? vc old)
      (throw (ex-info (str "a write starts from a value of " (:name type))
                      {:error :recognitum/not-a-value :type (:name type)})))
    (when-not (.deref ^clojure.lang.Volatile current)
      (throw (displaced-refusal (:name type) old)))))

(defn- make-own-memo
  "The `(own-memo d)` of `type`: the memory of `d`, a draft of `type`. Throws
  `:recognitum/not-a-draft` for anything else."
  [type]
  (fn [d]
    (let [m (when (draft? d) (marks-of d))]
      (when-not (and (instance? Memo m) (identical? type (.-type ^Memo m)))
        (throw (ex-info (str "not a draft of " (:name type) ": " (pr-str d))
                        {:error :recognitum/not-a-draft :type (:name type)})))
      m)))

(defn- make-own-draft
  "The `(own-draft d)` of `type`: `[data known memory]` of `d`, a draft of `type`: its
  entries, the checks its memory shows passing, and its memory. Throws as `own-memo` does."
  [type own-memo]
  (fn [d]
    (let [m (own-memo d)]
      [(.-data ^Draft d) (passes type (.-data ^Draft d) m) m])))

(defn- make-own-value
  "The `(own-value v)` of an unsealed `type`: the cell of `v`, the atom that holds its memory,
  as `strategy` reads it from `v`, a value of the class `vc`. Throws `:recognitum/not-a-value`
  for anything else, and `:recognitum/displaced` where `current`, a volatile, holds false."
  [{:keys [vc type current strategy]}]
  (fn [v]
    (when-not (instance? vc v)
      (throw (ex-info (str "not a value of " (:name type) ": " (pr-str v))
                      {:error :recognitum/not-a-value :type (:name type)})))
    (when-not (.deref ^clojure.lang.Volatile current)
      (throw (displaced-unsealed (:name type) v)))
    (proof/memory strategy v)))

(defn- make-own-subject
  "The `(own-subject x)` of `type`: what a run reads of `x`, a draft or, where `unsealed?`, a
  value of `type`, as `[data known memory cell]`: its entries, the checks its memory shows
  passing, its memory, and the cell that holds the memory. Throws as `own-memo` or `own-value`
  does."
  [{:keys [unsealed? type]} own-value own-memo]
  (fn [x]
    (if unsealed?
      (let [cell (own-value x)
            m @cell]
        [x (passes type x m) m cell])
      (let [m (own-memo x)
            data (.-data ^Draft x)]
        [data (passes type data m) m (.-cell ^Draft x)]))))

(defn- make-own-for-seal
  "The `(own-for-seal d)` of `type`: `[data known memory all? run-left]` of `d`, a draft of
  `type`: its entries, the checks its memory shows passing, its memory, whether those are
  every check, and, where they are not, a function of a map that runs the checks left. Throws
  as `own-memo` does."
  [{:keys [masks? type ids hot all-mask run*]} own-memo own-draft run-known]
  (fn [d]
    (if masks?
      (let [m (own-memo d)
            data (.-data ^Draft d)
            km (passes-mask type data m)]
        (if (== km all-mask)
          [data ids m true nil]
          (let [known (set-of hot km)]
            [data known m false (run-known km known)])))
      (let [[data known m] (own-draft d)]
        [data known m (empty? (minus ids known)) #(run* % known)]))))

(defn- make-check-group
  "The `(check-group groups entries)` of `type`: the arm that runs a batch's drafts and values
  of unsealed types, since only a type's own installed write can make them remember. `groups`
  holds one group per type, this type's first, each `[picked xs is kind]`:

  - `picked`, the checks that the batch's selection picks in the type;
  - `xs`, the vector of the batch's values and drafts;
  - `is`, the indices in `xs` of the type's drafts, or of its values where it is unsealed,
    ascending;
  - `kind`, the kind of run: nil for `check`'s, `:recheck` for `recheck`'s, or `:seal` for a
    seal's, which is `check`'s with the floor of each value added (the shape checks of its
    required fields and of the optional fields it holds).

  `entries` holds the jobs gathered so far, as [[recognitum.record.runs/run-jobs]] takes them.
  Adds a job for each draft or value of the group that has a check to run, and passes the
  rest of `groups` to the next type's installed write; the last one runs every job in one
  call of the engine and returns what `run-jobs` returns. Each draft or value remembers its run."
  [{:keys [masks? unsealed? type ids hot engine all-mask]} closure-of fetching-in own-memo own-subject remember!
   remember-m!]
  (fn [groups entries]
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
        (run-jobs (:run-all type) (in-group-order entries))))))

(defn- make-run-checks
  "The `(run-checks cache-key changes)` of a type without masks: the runner of the readers of
  the keys of `changes`, kept in `change-runs` under `cache-key` while `change-runs` has
  room."
  [{:keys [runner engine readers-v]} ^java.util.concurrent.ConcurrentHashMap change-runs]
  (fn [cache-key changes]
    (or (.get change-runs cache-key)
        (let [r (runner engine (reduce (fn [a k] (into a (readers-v k []))) #{} (keys changes)))]
          (when (< (.size change-runs) 1000) (.putIfAbsent change-runs cache-key r))
          r))))

(defn- make-whole-change
  "The `(whole-change old changes may-lack?)` of a type, for a change of a key that has a
  reader that reads a source: runs the readers of every key of `changes`, through the engine's
  `run-all`, on the view of `old` with `changes` applied, and throws as `refuse!` does."
  [{:keys [masks? ids hot all-mask readers-m readers-v removed run*]} refuse!]
  (fn [old changes may-lack?]
    (let [view (Changed. old changes removed)]
      (refuse! view
               (run* view (if masks?
                            (set-of hot (bit-and-not (long all-mask)
                                                     (long (reduce-kv (fn [m k _] (bit-or (long m) (long (readers-m k 0)))) 0 changes))))
                            (reduce (fn [a k] (reduce disj a (readers-v k [])))
                                    ids (keys changes))))
               may-lack?))))

(defn- make-change-many
  "The `(change-many old changes)` of `type`, for a change of several keys or a removal.
  `changes` maps each key changed to its new value, or to `removed` where the change removes
  it. Throws `:recognitum/undeclared-keys` where `changes` sets a key that `type` does not
  declare. Else runs the readers of the keys changed, and no other check, on the view of `old`
  with `changes` applied, and throws as `refuse!` does, the removal of a required field
  included; where a key changed has a reader that reads a source, calls `whole-change`
  instead.

  `key-guards` maps each declared key to its guard, or to `none` where its readers read a
  source. `key-bits` is nil, or, for a type without masks, a map from each declared key to its
  bit."
  [{:keys [masks? type hot all-mask readers-m readers-v required removed]} ^java.util.IdentityHashMap key-guards
   key-bits refuse! whole-change run-known run-checks]
  (fn [old ^clojure.lang.IPersistentMap changes]
    (let [view (Changed. old changes removed)
          it (.iterator ^Iterable changes)]
      (loop [mask 0, to-run #{}, may-lack? false, sourced? false]
        ;; with masks, `mask` gathers the bits of the readers of the keys changed; with key
        ;; bits, the bits of the keys changed; else `to-run` gathers the readers
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
                     may-lack?)))))))

(defn- make-seal-value
  "The `(seal-value v picked)` of an unsealed `type`, which seals `v`, a value of `type`,
  against the checks `picked`: it runs them, what they wait on and the floor of `v`, less what
  `v` is known to pass, makes `v` remember the run, and returns `v`. Throws as `own-subject`
  or `refuse!` does."
  [{:keys [type ids]} own-subject remember! refuse!]
  (fn [v picked]
    (let [[data known m0 cell] (own-subject v)
          to-run (minus (select/closure type (into (set/intersection ids (set picked))
                                                   (select/floor type data)))
                        known)
          result (when (seq to-run) (run type data (set/difference ids to-run)))]
      (when result (remember! cell data m0 known to-run result))
      (refuse! data (or result engine-passed) true)
      v)))

(defn- make-remember!
  "The `(remember! cell data m0 known to-run result forget)` of `type`, `forget` optional:
  writes into `cell` the memory that a run of the checks `to-run` on `data` leaves. `m0` is
  the memory the run started from, and `known` the checks `m0` showed passing.

  - Where `cell` still holds `m0`, the new memory shows `known`, less `forget`, plus what
    passed in `result`, less what failed.
  - Where another run has written `cell` since, the new memory shows what `cell` shows now,
    less what failed and less `forget`: a pass this run found may predate a forget that the
    other run wrote.

  Does nothing where `to-run` and `forget` are both empty. `memo` makes a memory from entries
  and the checks it shows passing; of these parts, it alone holds the access key."
  [type memo]
  (fn remember!
    ([cell data m0 known to-run result] (remember! cell data m0 known to-run result ()))
    ([cell data m0 known to-run result forget]
     (let [failed (keys (:failed result))]
       (when-not (or (and (empty? to-run) (empty? forget))
                     (compare-and-set! cell m0
                                       (memo data (reduce disj
                                                          (into (reduce disj known forget)
                                                                (passed-in to-run result))
                                                          failed))))
         (swap! cell #(memo data (reduce disj (passes type data %) (concat failed forget)))))))))

(defn- make-remember-m!
  "The `(remember-m! d m0 km tm result)` of a `type` with masks: what [[make-remember!]]'s
  function does, for a draft `d` and with nothing to forget. `km` is the mask of the checks
  known to pass, and `tm` the mask of those run. `memo-m` makes a memory from entries and a
  mask; of these parts, it alone holds the access key. `bits-of` gives the mask of a
  collection of ids, and `key-bits-of` the mask of a map's keys."
  [{:keys [type bits-of key-bits-of]} memo-m]
  (fn [^Draft d m0 km tm result]
    (let [data (.-data d)
          km (long km)
          tm (long tm)
          fm (key-bits-of (:failed result))
          bm (bits-of (:blocked result))]
      (when-not (compare-and-set! (.-cell d) m0
                                  (memo-m data (bit-and-not (bit-or km (bit-and-not tm (bit-or fm bm))) fm)))
        (swap! (.-cell d) #(memo-m data (bit-and-not (passes-mask type data %) fm)))))))

(defn- make-run-draft
  "The `(run-draft to-run subject forget)` of `type`: runs the checks `to-run` on the entries of
  `subject`, `[data known m0 cell]` as `own-subject` answers it, remembers the run through
  `remember!`, and returns its result."
  [{:keys [type ids]} remember!]
  (fn [to-run [data known m0 cell] forget]
    (let [result (run type data (set/difference ids to-run))]
      (remember! cell data m0 known to-run result forget)
      result)))

(defn- make-methods
  "The `:methods` of `spec` as the proof strategy's definition takes them: each signature, to
  the function its maker returns, given `current` and a `refuse` that throws the refusal of a
  displaced value, or of a displaced unsealed one where `unsealed?`. `toString` of no
  parameters is given a `current` that always holds true."
  [spec unsealed? current]
  (let [refuse (fn [v] (throw (if unsealed?
                                (displaced-unsealed (:name spec) v)
                                (displaced-refusal (:name spec) v))))]
    (into {} (for [[[n ps :as sig] make] (:methods spec)]
               [sig (if (and (= "toString" n) (empty? ps))
                      (make (volatile! true) refuse)
                      (make current refuse))]))))

(defn- make-definition
  "The definition of `spec` as the proof strategy takes it: its keys, interfaces, methods (as
  [[make-methods]] makes them) and `:instead`, and `:unsealed` where `unsealed?`."
  [spec unsealed? current]
  (cond-> {:keys (mapv :key (:fields spec))
           :interfaces (vec (:interfaces spec))
           :methods (make-methods spec unsealed? current)
           :instead (:instead spec)}
    unsealed? (assoc :unsealed true)))

(defn- make-type
  "The type map of `spec`, as [[compile-type]] compiles it, with the classes `vc` of its values
  and `dc` of its drafts, an empty volatile that [[define-type]] sets to the installed write
  once it installs that write, whether it is `unsealed?`, and its `Hot`."
  [spec strategy define run-all runner vc dc unsealed?]
  (let [t (compile-type spec strategy define run-all runner)]
    ;; an unsealed type's memories never show every check passing through a value of
    ;; its class: its `Hot` names Void, of which nothing is an instance
    (assoc t ::class vc ::draft-class dc ::gate (volatile! nil) ::unsealed unsealed?
           ::hot (hot-of (if unsealed? Void vc) dc strategy (:ids t) (:readers t) (::readers-v t)))))

(defn- make-bits-of
  "The `(bits-of xs)` of a type with masks: the mask of the ids in `xs`, a collection, each id's
  bit as `bits` gives it."
  [bits]
  (fn ^long [xs] (reduce (fn [^long a id] (bit-or a (long (bits id)))) 0 xs)))

(defn- make-key-bits-of
  "The `(key-bits-of m)` of a type with masks: the mask of the keys of `m`, a map of ids, each
  id's bit as `bits` gives it."
  [bits]
  (fn ^long [m] (reduce-kv (fn [^long a id _] (bit-or a (long (bits id)))) 0 m)))

(defn- make-run-of
  "The `run-of` of `type`: a map from each key of `declared` whose readers read no source to
  the runner of those readers alone."
  [{:keys [type declared readers runner engine]}]
  (into {} (for [k declared
                 :let [rs (get readers k #{})]
                 :when (not-any? #(:fetches? ((:by-id type) %)) rs)]
             [k (runner engine rs)])))

(defn- make-closure-of
  "The `(closure-of picked)` of `type`: `[closed mask]`, the checks of this type among `picked`
  with every check they wait on, as a set and as a mask (nil without masks). Kept in
  `closures` under `picked` while `closures` has room."
  [{:keys [type ids hot]} ^java.util.concurrent.ConcurrentHashMap closures]
  (fn [picked]
    (or (.get closures picked)
        (let [closed (select/closure type (set/intersection ids (set picked)))
              c [closed (mask-of hot closed)]]
          (when (< (.size closures) 1000) (.putIfAbsent closures picked c))
          c))))

(defn- make-fetching-in
  "The `(fetching-in picked)` of `type`: the checks of `picked` that read a source."
  [type]
  (fn [picked] (filter #(:fetches? ((:by-id type) %)) picked)))

(defn- make-guards
  "The key guards of `type`: a map from each key of `run-of` to its guard, made by the
  `:guard` of `spec` or, without one, by the guard maker that every such type shares. A key's
  guard runs the key's readers on the view of the old value with the key set. It throws
  `:recognitum/displaced` where the type is displaced, and `:recognitum/check-failed` where a
  reader fails."
  [spec {:keys [type current]} run-of clean?]
  (let [make (or (:guard spec) (guard-maker With))
        refuse (fn [old result]
                 (throw (if result
                          (check-failed type (report type result))
                          (displaced-refusal (:name type) old))))]
    (into {} (for [[k r] run-of] [k (make current r k clean? refuse)]))))

(defn- make-key-guards
  "The `key-guards` of a type: an IdentityHashMap from each key of `declared` to its guard in
  `guards`, or to `none` where its readers read a source."
  [{:keys [declared]} guards]
  (let [m (java.util.IdentityHashMap.)]
    (doseq [k declared] (.put m k (get guards k none)))
    m))

(defn- make-key-bits
  "The `key-bits` of a type: for a type without masks that declares at most 64 keys, an
  IdentityHashMap from each key of `declared` to a bit of a `long`; else nil."
  [{:keys [masks? declared]}]
  (when (and (not masks?) (<= (count declared) 64))
    (let [m (java.util.IdentityHashMap.)]
      (doseq [[i k] (map-indexed vector (sort-by str declared))] (.put m k (bit-shift-left 1 i)))
      m)))

(defn- make-carry
  "The carry of an unsealed `type`: `(carry old changes)` returns a new cell for the value that
  a change of `old` makes. Its memory is `old`'s, with the keys of `changes` added to the keys
  written, so that the new value forgets the checks that read them. Throws as `own-value` does
  for `old`, and `:recognitum/undeclared-keys` where `changes` holds a key that `type` does not
  declare."
  [type own-value]
  (fn [old changes]
    (let [cell (own-value old)]
      (refuse-undeclared! type (keys changes))
      (let [mo @cell]
        (atom (if (and (instance? Memo mo) (some? (.-proof ^Memo mo)))
                (let [^Memo mo mo]
                  (Memo. (.-type mo) (.-base mo) (.-passes mo) (into (.-written mo) (keys changes))
                         (.-proof mo) (.-mask mo)))
                mo))))))

(defn- parts-of
  "The parts of a type: the map that the `make-*` builders of its functions destructure. It
  holds `:type`, the type map; `:strategy`, `:runner`, `:vc` (the class of its values),
  `:unsealed?` and `:current`, as [[define-type]] has them; and what the builders read of the
  type map and of its `Hot`, such as `:ids`, `:masks?` and `:readers`."
  [type strategy runner vc unsealed? current]
  (let [ids (:ids type)
        ^Hot hot (::hot type)
        masks? (some? (.-bits hot))
        all-mask (.-all hot)
        bits (.-bits hot)
        bits-of (make-bits-of bits)
        key-bits-of (make-key-bits-of bits)
        engine (:engine type)
        run* (::run type)
        declared (:keys type)
        declared? (member-of declared)
        required-v (::required-v type)
        required (:required type)
        readers (:readers type)
        readers-v (::readers-v type)
        removed (proof/removed strategy)
        fetching-m (when masks? (mask-of hot (filter #(:fetches? ((:by-id type) %)) ids)))
        readers-m (.-readers-m hot)]
    {:type type :strategy strategy :runner runner :vc vc :unsealed? unsealed? :current current
     :ids ids :hot hot :masks? masks? :all-mask all-mask :bits bits :bits-of bits-of
     :key-bits-of key-bits-of :engine engine :run* run* :declared declared :declared? declared?
     :required-v required-v :required required :readers readers :readers-v readers-v
     :removed removed :fetching-m fetching-m :readers-m readers-m}))

(defn- make-construct
  "The `(construct x y)` of `type`: a value of the entries of the map `x`. Throws
  `:recognitum/displaced-constructor`, with the remedy `y` as its advice, where `current`, a
  volatile, holds false, and `:recognitum/undeclared-keys` where `x` has a key that
  `declared?` denies. Where `unsealed?`, `build` makes the value, and no check runs; else
  every check runs through `run*`, and `seal!` seals the entries or throws."
  [{:keys [type current declared? unsealed? run*]} build seal!]
  (fn [x y]
    (let [data (proof/plain-map x)]
      (when-not (.deref ^clojure.lang.Volatile current)
        (throw (displaced-constructor (:name type) y)))
      (when-not (all-declared? declared? data) (refuse-undeclared! type (keys data)))
      (if unsealed?
        (build data)
        (seal! data (run* data #{}) true)))))

(defn- make-seal
  "The `(seal x y)` of `type`. Where `unsealed?`, `seal-value` of the value `x` against the
  checks `y`. Else the seal of the draft `x`, as `own-for-seal` reads it:

  - it throws `:recognitum/displaced-constructor` where `current`, a volatile, holds false,
    and `:recognitum/undeclared-keys` where the draft has a key that `declared?` denies;
  - it runs the checks the draft is not known to pass;
  - where one fails or a required field is absent (`clean?`, `lacks?`), the draft remembers
    the run through `remember!`, and the seal throws `:recognitum/check-failed`;
  - else it returns the draft's entries sealed by `seal-data`, and the draft remembers that
    every check passes."
  [{:keys [unsealed? type ids all-mask current declared?]} clean? lacks? remember! own-for-seal seal-value seal-data]
  (fn [x y]
    (if unsealed?
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
            (let [v (seal-data (with-meta-of data x))]
              (when-not all-pass?
                (compare-and-set! (.-cell ^Draft x) m0 (Memo. type v ids #{} v all-mask)))
              v)))))))

(defn- make-draft-of
  "The `(draft-of x)` of `type`: a draft of `x`, a value of the class `vc`, whose memory has `x`
  as its proof and so shows every check passing. Throws `:recognitum/no-drafts` where
  `unsealed?`, and `:recognitum/not-a-value` for anything but a value of `vc`."
  [{:keys [unsealed? type vc ids all-mask]}]
  (fn [x]
    (cond unsealed? (throw (no-drafts (:name type)))
          (instance? vc x) (Draft. (proof/plain-map x) (atom (Memo. type x ids #{} x all-mask)) (meta x) 0)
          :else (throw (ex-info (str "not a value of " (:name type)) {:error :recognitum/not-a-value})))))

(defn- make-rewrite
  "The `(rewrite x y)` of a type: the draft `x` with its entries replaced by those of the map
  `y`, forgetting the checks that read a key that changed; `x` itself where nothing changed.
  Throws as `own-draft` does."
  [own-draft]
  (fn [x y]
    (let [[data] (own-draft x)
          y (proof/plain-map y)
          changed (changed-keys data y)]
      (if (empty? changed)
        x
        (rewritten x y #(into % changed) (odd-after x y changed))))))

(defn- make-clean-draft
  "The `(clean-draft x)` of `type`: the draft `x` without the keys `type` does not declare, or
  `x` itself where it has none. Throws `:recognitum/no-drafts` where `unsealed?`, and else as
  `own-draft` does."
  [{:keys [unsealed? type]} own-draft]
  (fn [x]
    (let [_ (when unsealed? (throw (no-drafts (:name type))))
          [data] (own-draft x)
          kept (select-keys data (:keys type))]
      (if (= (count kept) (count data))
        x
        (rewritten x kept #(into % (remove (:keys type)) (keys data)) 0)))))

(defn- make-check
  "The `(check x y)` of `type`, where `x` is a draft or, where the type is unsealed, a value:
  runs on `x`, through `run-draft`, the checks of `type` that `y` names and the checks they
  wait on, less those `x` is known to pass. `x` remembers the run. Returns the run's result."
  [{:keys [type ids]} own-subject run-draft]
  (fn [x y]
    (let [[_ known :as own] (own-subject x)
          named (set/intersection ids (set y))]
      (run-draft (minus (select/closure type named) known) own ()))))

(defn- make-recheck
  "The `(recheck x y)` of `type`: as [[make-check]]'s function, but the checks `y` names run
  whether or not `x` is known to pass them. Of those, the ones that read a source, as
  `fetching-in` finds them, are forgotten, and remembered again only where this run passes them."
  [{:keys [type ids]} own-subject run-draft fetching-in]
  (fn [x y]
    (let [[_ known :as own] (own-subject x)
          named (set/intersection ids (set y))]
      (run-draft (into named (set/difference (select/closure type named) known)) own
                 (fetching-in named)))))

(defn- make-open
  "The `(open)` of `type`: a new empty draft, whose memory is `nothing`, the memory of a draft
  that passes no check. Refuses where `unsealed?`."
  [{:keys [unsealed? type]} nothing]
  (fn []
    (if unsealed?
      (throw (no-drafts (:name type)))
      (Draft. {} (atom nothing) nil 0))))

(defn- displace-predecessor!
  "Where `spec` names its type, records `type` as the latest definition of that name, as
  [[succeed!]] does, and displaces the definition it replaces, if any."
  [spec type]
  (when-let [n (:name spec)]
    (when-let [displaced (succeed! n type)]
      ((gate displaced) ::displace nil nil))))

(defn define-type
  "Defines a type and returns its type map, which holds no access key. `spec`:

  - `:name`, a qualified symbol, which also names the type's class;
  - `:fields`, each `{:key :sym :optional?}`;
  - `:checks`, each `{:id :waits :run}` and optionally `:concerns`, `:doc`, `:reads` (the keys it
    reads), `:sources` (the sources it reads, compared with `=` by the selection
    [[recognitum.select/fetching]]), `:fetches?`, `:shape-of` (the key of the field it is the
    shape check of) and `:gate` (a key: where it is absent, the check passes without running).
    `:run` is a compiled check of the engine. A check waits on the checks in its `:waits` and
    on the shape check of each key it reads, as [[waits-of]] says. The shape check of an
    optional field passes where its field is absent;
  - `:interfaces`, the interfaces every value of the type implements (a protocol's among
    them), and `:methods`, a map from each method's signature, as the proof strategy's
    definition takes it, to a fn of `current` and `refuse` that returns the method's function.
    That function takes the value first and calls `refuse` with it where `current`, a
    volatile, holds false. `toString` of no parameters is given a `current` that always holds
    true;
  - optionally `:unsealed true`, for a type as `rec/defproven-in` defines one: its values are
    made and written with no check run and remember what passed, and the type has no drafts;
  - optionally `:guard`, the value of a [[recognitum.record.views/guard-maker]] form that the
    definition's expansion holds, and `:change`, the value of a
    [[recognitum.record.views/change-guard-maker]] form there. Without them, the type uses the
    makers compiled in this namespace, which every such type shares;
  - optionally `:instead`, a string that closes the message the class's constructor throws
    when code without the access key calls it: what to call instead.

  `wiring` names the proof `:strategy` and the engine's `:define`, `:run-all` and `:runner`,
  which runs the checks that read no source on the calling thread.

  Defining a type under a name that already names a type is a redefinition: the definition
  of that name current before it is displaced, whatever the name's namespace maps the name to
  now, and even where that namespace was removed. Its values stay instances of their class
  and are no longer sealed:

  - a write that changes one, and every method but `toString` called with one, throws
    `:recognitum/displaced`;
  - [[recognitum.record.values/draft]] of one gives a draft of the type's current
    definition, where the name still names one;
  - [[recognitum.record.values/make]] with the displaced type map, and
    [[recognitum.record.values/seal]] of a draft of its class, throw
    `:recognitum/displaced-constructor`, so a constructor or a class held from before makes
    nothing."
  [spec {:keys [strategy define run-all runner]}]
  (let [current (volatile! true)
        unsealed? (true? (:unsealed spec))
        h (proof/define-type strategy (:name spec) (make-definition spec unsealed? current))
        [vc dc] (proof/classes h)
        type (make-type spec strategy define run-all runner vc dc unsealed?)
        parts (parts-of type strategy runner vc unsealed? current)
        {:keys [hot masks? removed]} parts
        nothing (Memo. type nil #{} #{} nil (when masks? 0))
        memo (fn [data ids]
               (if (empty? ids)
                 nothing
                 (let [m (proof/open h)
                       mask (mask-of hot ids)]
                   (proof/mark! h m (PassKey. data ids mask))
                   (Memo. type data ids #{} m mask))))
        ;; `memo` of the checks of `mask`, for a type with masks
        memo-m (fn [data ^long mask]
                 (if (zero? mask)
                   nothing
                   (let [m (proof/open h)
                         ids (set-of hot mask)]
                     (proof/mark! h m (PassKey. data ids mask))
                     (Memo. type data ids #{} m mask))))
        lacks? (make-lacks? parts)
        clean (volatile! nil)
        clean? (make-clean? clean)
        refuse! (make-refuse! type clean?)
        ;; `data` sealed, where `result`, the run of every check on it, is clean and, where
        ;; `may-lack?`, no required field is absent; else throws as `refuse!` does
        seal! (fn [data result may-lack?]
                (if (and (clean? result) (not (and may-lack? (lacks? data))))
                  (proof/seal h data)
                  (do (refuse! data result may-lack?)
                      (proof/seal h data))))
        run-of (make-run-of parts)
        own! (make-own! parts)
        own-memo (make-own-memo type)
        own-draft (make-own-draft type own-memo)
        own-value (make-own-value parts)
        own-subject (make-own-subject parts own-value own-memo)
        ;; each mask of known checks, to the runner of the checks it leaves, where none of those
        ;; reads a source
        runs (java.util.concurrent.ConcurrentHashMap.)
        run-known (make-run-known parts runs)
        own-for-seal (make-own-for-seal parts own-memo own-draft run-known)
        remember! (make-remember! type memo)
        remember-m! (make-remember-m! parts memo-m)
        closures (java.util.concurrent.ConcurrentHashMap.)
        closure-of (make-closure-of parts closures)
        fetching-in (make-fetching-in type)
        check-group (make-check-group parts closure-of fetching-in own-memo own-subject remember! remember-m!)
        run-draft (make-run-draft parts remember!)
        guards (make-guards spec parts run-of clean?)
        key-guards (make-key-guards parts guards)
        key-bits (make-key-bits parts)
        ;; for a type without masks: the keys that a change of several keys changes, as their
        ;; `key-bits` mask or else as the set of their readers, to the runner of those readers,
        ;; where none of them reads a source
        change-runs (java.util.concurrent.ConcurrentHashMap.)
        run-checks (make-run-checks parts change-runs)
        whole-change (make-whole-change parts refuse!)
        change-many (make-change-many parts key-guards key-bits refuse! whole-change run-known run-checks)
        ;; the change guard, `(cg old changes)`: a change that sets one key goes to that key's
        ;; guard, and any other to `change-many` or `whole-change`
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
        seal-value (make-seal-value parts own-subject remember! refuse!)
        ;; a value of this unsealed type, of the entries `data`
        build (fn [data] (proof/build h data (atom nothing)))
        construct (make-construct parts build seal!)
        ;; `data`, which every check passes, sealed
        seal-data (fn [data] (proof/seal h data))
        seal (make-seal parts clean? lacks? remember! own-for-seal seal-value seal-data)
        draft-of (make-draft-of parts)
        rewrite (make-rewrite own-draft)
        clean-draft (make-clean-draft parts own-draft)
        check (make-check parts own-subject run-draft)
        recheck (make-recheck parts own-subject run-draft fetching-in)
        open (make-open parts nothing)
        ;; the installed write. Its three-argument arity, which `installed` and each class's
        ;; `gate()` reach without the access key, holds the arms and serves both kinds of type;
        ;; an unsealed type's strategy calls no other arity.
        write-all (fn
                    ([old entries] (write old entries))
                    ;; the change guard takes every change of one key, so this arity is never called
                    ([old entries _ _] (write old entries))
                    ([op x y]
                     (case op
                       ::make (construct x y)
                       ::open (open)
                       ::draft-of (draft-of x)
                       ::rewrite (rewrite x y)
                       ::clean (clean-draft x)
                       ::seal (seal x y)
                       ::check (check x y)
                       ::check-all (check-group x y)
                       ::type type
                       ::current? @current
                ;; whether `x` is a value sealed under this definition, which is current
                       ::sealed? (and (.deref ^clojure.lang.Volatile current) (proof/proven? h x))
                       ::displace (do (vreset! current false) nil)
                       ::recheck (recheck x y))))]
    (if unsealed?
      ;; each change of a value calls the carry, which gives the new value the old value's
      ;; memory, with the keys the change writes added to the keys written
      (proof/install-carry!
       h
       write-all
       (make-carry type own-value))
      (proof/install-write!
       h
       write-all
       (fn [k] (get guards k))
       change-guard))
    (vreset! (::gate type) (proof/installed strategy vc))
    (displace-predecessor! spec type)
    type))
