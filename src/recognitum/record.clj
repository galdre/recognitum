(ns recognitum.record
  "The record layer: types whose values read as maps and carry proof that their checks passed,
  drafts that remember which checks pass, checked writes, optional fields and closed types.
  [[define-type]] defines a type from compiled checks, a proof strategy and a check engine,
  and names neither. It compiles the spec into the type map, asks the strategy for the type's
  classes and the handle that holds its key, builds the type's write from what its children
  provide (`recognitum.record.memory` and `.draft` for what passes, `.views` for what a write's
  checks read, `.runs` for running checks, `.reports` for refusals), installs it, and displaces
  the definition it succeeds. What acts on values of any type it defined is in
  `recognitum.record.values`, `.runs`, `.probe`, `.types` and `.walk`.

  The key that mints a type's values and marks its drafts never leaves the closure
  [[define-type]] builds: it is reachable only through the type's installed write, its key
  guards and its change guard, each of which runs the checks it stands for."
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
  ;; each type name, to a weak reference to the definition that a later definition of the name
  ;; displaces. Weak, so that a definition nothing else holds is collected with its class: its
  ;; values, drafts, constructors and class all reach it, and nothing else needs displacing.
  (java.util.concurrent.ConcurrentHashMap.))

(defonce ^:private cleared
  ;; the references of `definitions` whose definition was collected
  (java.lang.ref.ReferenceQueue.))

(defn- succeed!
  "Makes `type` the definition of type name `n` that the next definition of `n` displaces.
  Returns the definition `type` succeeds, which it displaces, or nil. One atomic replacement,
  so of two definitions of `n` at once, each succeeds a different one and the later stays."
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

(defn- present-only
  "`run`, where the field `k` is present; passing where it is absent."
  [k run]
  (fn [value] (if (contains? value k) (run value) true)))

;;; ------------------------------------------------------------------ one-key writes

;; The view of the types that place no view of their own.
(view-type With)

;;; ------------------------------------------------------------------ definition

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
     ;; each selection, to whether it selects nothing in the type
     ::nothing (java.util.concurrent.ConcurrentHashMap.)
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

(defn- make-run-known
  "The `(run-known km known)` of a type with masks: a run of the checks that the mask `km` of
  checks known to pass leaves, `known` as a set. Where none of those reads a source, the
  runner over them, kept in `runs` under `km`; past 1000 masks, a mask not kept runs every
  check but the known through `run*`, building nothing."
  [^java.util.concurrent.ConcurrentHashMap runs fetching-m runner engine hot all-mask run*]
  (fn [^long km known]
    (or (.get runs km)
        (if (and (< (.size runs) 1000) (zero? (bit-and-not (long fetching-m) km)))
          (let [r (runner engine (set-of hot (bit-and-not all-mask km)))
                f (fn [data] (r data nil))]
            (.putIfAbsent runs km f)
            f)
          (fn [data] (run* data known))))))

(defn- make-clean?
  "The `(clean? result)` of a type: whether a run's result has nothing failed or blocked, first
  by identity with the result last found clean, which `clean`, a volatile, holds, as results
  are immutable."
  [clean]
  (fn [result]
    (or (identical? result (.deref ^clojure.lang.Volatile clean))
        (when-not (or (seq (:failed result)) (seq (:blocked result)))
          (vreset! clean result)
          true))))

(defn- make-lacks?
  "The `(lacks? data)` of a type: whether `data` lacks one of the required fields
  `required-v`."
  [required-v]
  (fn [data] (not (reduce (fn [_ k] (if (contains? data k) true (reduced false))) true required-v))))

(defn- make-refuse!
  "The `(refuse! data result may-lack?)` of `type`: throws the failure of `result`, the run of
  the checks on `data`, where a check failed or, where `may-lack?`, a required field is
  absent."
  [type clean?]
  (fn [data result may-lack?]
    (let [absent (when may-lack? (missing type data))]
      (when (or absent (not (clean? result)))
        (throw (check-failed type (when-not (clean? result) (report type result)) absent))))))

(defn- make-own!
  "The `(own! old)` of `type`: refuses `old` where it is not a value of the class `vc`, or
  where `current`, a volatile, holds false."
  [vc type current]
  (fn [old]
    (when-not (instance? vc old)
      (throw (ex-info (str "a write starts from a value of " (:name type))
                      {:error :recognitum/not-a-value :type (:name type)})))
    (when-not (.deref ^clojure.lang.Volatile current)
      (throw (displaced-refusal (:name type) old)))))

(defn- make-own-memo
  "The `(own-memo d)` of `type`: the memory of `d`, a draft of `type`; refuses anything else."
  [type]
  (fn [d]
    (let [m (when (draft? d) (marks-of d))]
      (when-not (and (instance? Memo m) (identical? type (.-type ^Memo m)))
        (throw (ex-info (str "not a draft of " (:name type) ": " (pr-str d))
                        {:error :recognitum/not-a-draft :type (:name type)})))
      m)))

(defn- make-own-draft
  "The `(own-draft d)` of `type`: `[data passes memory]` of `d`, a draft of `type`, through
  `own-memo`."
  [type own-memo]
  (fn [d]
    (let [m (own-memo d)]
      [(.-data ^Draft d) (passes type (.-data ^Draft d) m) m])))

(defn- make-own-value
  "The `(own-value v)` of an unsealed `type`: the memory cell of `v`, a value of the class `vc`,
  which `strategy` holds; refuses anything else, and `v` where `current`, a volatile, holds
  false."
  [vc type current strategy]
  (fn [v]
    (when-not (instance? vc v)
      (throw (ex-info (str "not a value of " (:name type) ": " (pr-str v))
                      {:error :recognitum/not-a-value :type (:name type)})))
    (when-not (.deref ^clojure.lang.Volatile current)
      (throw (displaced-unsealed (:name type) v)))
    (proof/memory strategy v)))

(defn- make-own-subject
  "The `(own-subject x)` of `type`: what a run reads of `x`, a draft or, where `unsealed?`, a
  value of `type`, as `[entries passes memory cell]`, the cell the one that holds the memory."
  [unsealed? type own-value own-memo]
  (fn [x]
    (if unsealed?
      (let [cell (own-value x)
            m @cell]
        [x (passes type x m) m cell])
      (let [m (own-memo x)
            data (.-data ^Draft x)]
        [data (passes type data m) m (.-cell ^Draft x)]))))

(defn- make-own-for-seal
  "The `(own-for-seal d)` of `type`: of `d`, a draft of `type`, its entries, what it passes, its
  memory, whether it passes every check, and a run of the checks left; through the mask where
  `masks?`."
  [masks? type ids hot all-mask own-memo own-draft run-known run*]
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
  "The `(check-group groups entries)` of `type`. `groups`, each `[picked xs is kind]`: the
  checks a selection picks in a type, a vector of values, the indices in `xs` of the drafts of
  the type, or of its values where it is unsealed, ascending, and the kind of run: nil for
  check's, `:recheck` for recheck's, `:seal` for seal's (check's, with the floor of each
  value). This type's group comes first; each other type's gate takes its own. Each draft or
  value is read once, and runs where it has anything to run."
  [masks? unsealed? type ids hot engine all-mask closure-of fetching-in own-memo own-subject remember! remember-m!]
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
  "The `(run-checks cache-key changes)` of a type without masks: a runner of the readers of the
  keys of `changes`, kept in `change-runs` under `cache-key`; past 1000, a set not kept is
  built anew."
  [^java.util.concurrent.ConcurrentHashMap change-runs runner engine readers-v]
  (fn [cache-key changes]
    (or (.get change-runs cache-key)
        (let [r (runner engine (reduce (fn [a k] (into a (readers-v k []))) #{} (keys changes)))]
          (when (< (.size change-runs) 1000) (.putIfAbsent change-runs cache-key r))
          r))))

(defn- make-whole-change
  "The `(whole-change old changes may-lack?)` of a type: a change of a key whose readers read a
  source runs every check that reads a key changed, on the view of `old` with `changes`
  applied, and refuses as `refuse!` does."
  [masks? ids hot all-mask readers-m readers-v removed refuse! run*]
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
  "The `(change-many old changes)` of `type`: a change of several keys, or a removal, runs the
  readers of the keys changed on the view of `old` with `changes` applied, and nothing else;
  where a key changed has readers that read a source, it is `whole-change`. `key-guards` maps
  each declared key to its guard, or to `none`; `key-bits`, where a type without masks has
  one, each declared key to a bit."
  [masks? type hot all-mask readers-m readers-v required removed ^java.util.IdentityHashMap key-guards
   key-bits refuse! whole-change run-known run-checks]
  (fn [old ^clojure.lang.IPersistentMap changes]
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
                     may-lack?)))))))

(defn- make-seal-value
  "The `(seal-value v picked)` of an unsealed `type`, which seals `v`, a value of `type`, against
  the checks `picked`: it runs them, what they wait on and the floor, less what `v` passes,
  remembers the run, and returns `v` or throws."
  [type ids own-subject remember! refuse!]
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
  "The `(remember! cell data m0 known to-run result forget?)` of `type`: a run writes what it
  found over the memory `m0` it started from, less `forget`, into `cell`. Where another run
  has written since, it only forgets what failed and `forget`: a pass it found may predate a
  forget written since. `memo` makes a memory; it is the only part that holds the type's key."
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
  "The `(remember-m! d m0 km tm result)` of a `type` with masks: [[make-remember!]]'s function
  for a draft `d`, with nothing more to forget; `km` the mask of the checks known to pass, `tm`
  of those run. `memo-m` makes a memory from a mask; it is the only part that holds the type's
  key. `bits-of` and `key-bits-of` give the mask of a collection of ids and of a map's keys."
  [type memo-m bits-of key-bits-of]
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
  `subject`, `[data known m0 cell]` as an own-subject answers it, remembers the run through
  `remember!`, and returns its result."
  [type ids remember!]
  (fn [to-run [data known m0 cell] forget]
    (let [result (run type data (set/difference ids to-run))]
      (remember! cell data m0 known to-run result forget)
      result)))

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
    same way;
  - optionally `:instead`, a string: what a caller should do in place of calling the type's
    class's constructor, whose refusal, without the key, closes with it.

  `wiring` names the proof `:strategy` and the engine's `:define`, `:run-all` and `:runner`,
  which runs the checks that read no source on the calling thread. Defining a
  type under a name already defined is redefinition: the definition of that name current
  before it is displaced, whatever the name's namespace maps the name to now, or whether the
  namespace was removed. Its values stay values of their class and are no longer
  proven: a write that changes one, and every method but `toString` called with one, throws
  the refusal `:recognitum/displaced`. [[draft]] of one gives a draft of the type's current
  definition. [[make]] with the displaced definition, and [[seal]] of a draft of its class,
  throw the refusal `:recognitum/displaced-constructor`, so a constructor or a class held from
  before makes nothing."
  [spec {:keys [strategy define run-all runner]}]
  (let [current (volatile! true)
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
                                                  (make current refuse))])))
                     :instead (:instead spec)}
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
        lacks? (make-lacks? required-v)
        readers (:readers type)
        readers-v (::readers-v type)
        removed (proof/removed strategy)
        clean (volatile! nil)
        clean? (make-clean? clean)
        refuse! (make-refuse! type clean?)
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
        own! (make-own! vc type current)
        own-memo (make-own-memo type)
        own-draft (make-own-draft type own-memo)
        own-value (make-own-value vc type current strategy)
        own-subject (make-own-subject unsealed? type own-value own-memo)
        ;; a draft's entries, what it passes, its memory, and whether it passes every check:
        ;; through the mask where the type has one
        ;; each mask of passing checks asked for, to a run of the checks it leaves: the runner
        ;; over those checks where none reads a source, else every check but the known
        runs (java.util.concurrent.ConcurrentHashMap.)
        fetching-m (when masks? (mask-of hot (filter #(:fetches? ((:by-id type) %)) ids)))
        run-known (make-run-known runs fetching-m runner engine hot all-mask run*)
        own-for-seal (make-own-for-seal masks? type ids hot all-mask own-memo own-draft run-known run*)
        remember! (make-remember! type memo)
        remember-m! (make-remember-m! type memo-m bits-of key-bits-of)
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
        check-group (make-check-group masks? unsealed? type ids hot engine all-mask closure-of fetching-in
                                      own-memo own-subject remember! remember-m!)
        run-draft (make-run-draft type ids remember!)
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
        run-checks (make-run-checks change-runs runner engine readers-v)
        whole-change (make-whole-change masks? ids hot all-mask readers-m readers-v removed refuse! run*)
        change-many (make-change-many masks? type hot all-mask readers-m readers-v required removed key-guards
                                      key-bits refuse! whole-change run-known run-checks)
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
        seal-value (make-seal-value type ids own-subject remember! refuse!)
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
                                (Draft. {} (atom nothing) nil 0))
                       ::draft-of (cond unsealed? (throw (no-drafts (:name type)))
                                        (instance? vc x) (Draft. (proof/plain-map x) (atom (Memo. type x ids #{} x all-mask)) (meta x) 0)
                                        :else (throw (ex-info (str "not a value of " (:name type)) {:error :recognitum/not-a-value})))
                       ::rewrite (let [[data] (own-draft x)
                                       y (proof/plain-map y)
                                       changed (changed-keys data y)]
                                   (if (empty? changed)
                                     x
                                     (rewritten x y #(into % changed) (odd-after x y changed))))
                       ::clean (let [_ (when unsealed? (throw (no-drafts (:name type))))
                                     [data] (own-draft x)
                                     kept (select-keys data (:keys type))]
                                 (if (= (count kept) (count data))
                                   x
                                   (rewritten x kept #(into % (remove (:keys type)) (keys data)) 0)))
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
    (when-let [n (:name spec)]
      (when-let [displaced (succeed! n type)]
        ((gate displaced) ::displace nil nil)))
    type))
