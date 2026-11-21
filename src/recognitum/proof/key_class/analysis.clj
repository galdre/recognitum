(ns recognitum.proof.key-class.analysis
  "The analysis of a key-class definition: what defining it takes, or why it is refused.

  - [[analysis]] answers the interfaces, the plan of forwarded methods, the print preferences
    and the other parts that `recognitum.proof.key-class` needs to define the type, or a
    refusal.
  - [[refusal]] answers the refusal alone.
  - [[outranked]] answers the refusal of a print preference that cannot be set.

  Nothing here defines a class, holds an access key or changes a multimethod. Hidden: how the
  methods of the listed interfaces are resolved against the map's, and which default bodies
  compete."
  (:require [clojure.string :as str]
            [recognitum.proof])
  (:import [clojure.lang DynamicClassLoader MultiFn RT]
           [java.lang.reflect Method Modifier]))

(set! *warn-on-reflection* true)

(def ^:private max-keys
  "The most keys that a definition may declare. T has a constructor that takes every field,
  which the assoc of each key calls, and a JVM method takes at most 255 parameter slots, of
  which `this`, the metadata, `ext` and the count take four. A defrecord's constructor has the
  same bound."
  250)

(def ^:private max-words
  "The most characters that a definition's `:instead` may hold. T's constructor loads its
  message, which holds those words, as one constant of the class file, and a constant holds at
  most 65535 bytes. A character takes at most three bytes, so this bound leaves room for the
  message's opening words and the class name."
  10000)

(defn- refusal-of
  "A refusal of `kind`, whose message says `msg` of `x`, with `more` (`:method`, `:interfaces`)."
  [kind msg x more]
  (merge {:kind kind :message (str "refused definition: " msg ": " (pr-str x))} more))

(defn- refuse
  "Throws, to end the analysis of a definition, the refusal that [[refusal-of]] makes of its
  arguments. [[analysis]] catches it."
  [kind msg x & {:as more}]
  (throw (ex-info "refused" {:recognitum.proof.key-class/refusal (refusal-of kind msg x more)})))

(defn- method-of
  "`[name arity]` of the method named `n` with parameters `params`."
  [n params]
  [(symbol n) (count params)])

(defn- sig-method
  "`[name arity]` of the signature `[nm spec]`, the name spelled as the signature spells it."
  [[nm spec]]
  [(if (symbol? nm) nm (symbol nm)) (if (vector? spec) (count spec) spec)])

(defn- without-functions
  "`definition` as a refusal's message prints it: its signatures without their functions, so
  the words depend on no function."
  [definition]
  (if (and (map? definition) (map? (:methods definition)))
    (update definition :methods (comp vec keys))
    definition))

(def ^:private own
  "The [name parameter-types] of the methods T declares for itself, statics included."
  #{["claim" [(class (object-array 0)) Object]] ["install" [Object Object Object (class (object-array 0)) Object]] ["gate" []]
    ["create" [clojure.lang.IPersistentMap]] ["delta$" [Object Object]] ["index$" [Object]] ["plain" [Object]] ["withExt" [clojure.lang.IPersistentMap]]
    ["writeReplace" []] ["getLookupThunk" [clojure.lang.Keyword]] ["memory$" []]
    ["readObject" [java.io.ObjectInputStream]] ["meta" []] ["withMeta" [clojure.lang.IPersistentMap]]
    ["asTransient" []] ["valAt" [Object]] ["valAt" [Object Object]] ["containsKey" [Object]]
    ["entryAt" [Object]] ["count" []] ["seq" []] ["iterator" []] ["keyIterator" []] ["valIterator" []] ["assoc" [Object Object]]
    ["assocEx" [Object Object]] ["without" [Object]] ["cons" [Object]] ["empty" []]})

(defn- own?
  "Whether T declares a method `n` of `params` for itself: in [[own]], or the assoc of one
  declared key."
  [n params]
  (or (contains? own [n params])
      (and (= [Object] params) (some? (re-matches #"assoc\$\d+" n)))))

(defn- implemented?
  "Whether T has a method `n` of `params` without the definition: its own or its map's."
  [n params]
  (or (own? n params)
      (try (.getMethod clojure.lang.APersistentMap n (into-array Class params)) true
           (catch NoSuchMethodException _ false))))

(defn- class-implemented?
  "Whether a class T extends, or T itself, declares method `n` of `params`: a body that wins
  over every interface's default."
  [n params]
  (or (own? n params)
      (try (not (.isInterface (.getDeclaringClass (.getMethod clojure.lang.APersistentMap n (into-array Class params)))))
           (catch NoSuchMethodException _ false))))

(defn- interface-methods
  "The instance methods interface `c` declares or inherits, as [[name params] Method] pairs."
  [^Class c]
  (for [^Method m (.getMethods c)
        :when (not (Modifier/isStatic (.getModifiers m)))]
    [[(.getName m) (vec (.getParameterTypes m))] m]))

(defn- members
  "The instance methods `c` declares or inherits, as [[name params] Method] pairs; of
  `Object`, `toString` alone. Refuses a class that is neither an interface nor `Object`."
  [^Class c]
  (cond
    (= c Object)     [[["toString" []] (.getMethod Object "toString" (make-array Class 0))]]
    (.isInterface c) (interface-methods c)
    :else            (refuse :not-an-interface "not an interface" c :interfaces [c])))

(def ^:private map-methods
  "The methods of the interfaces T has as a map, by [name params]: their defaults compete
  with a listed interface's."
  (group-by first (mapcat interface-methods (filter #(.isInterface ^Class %) (supers clojure.lang.APersistentMap)))))

(defn- maximal
  "The methods of `ms` whose declaring interface no other declaring interface of `ms` extends."
  [ms]
  (let [owners (set (map #(.getDeclaringClass ^Method %) ms))]
    (remove (fn [^Method m]
              (let [a (.getDeclaringClass m)]
                (some (fn [^Class b] (and (not= a b) (.isAssignableFrom a b))) owners)))
            ms)))

(def ^:private draft-interfaces
  "The interfaces every draft class implements."
  [java.util.function.BiConsumer java.util.function.Predicate])

(defn- check-shape!
  "Refuses a definition:

  - that is not `{:interfaces [class ...] :methods {signature f}}`;
  - whose keys are not distinct keywords, or are more than [[max-keys]];
  - whose `:unsealed` is not true, false or nil;
  - one of whose `interfaces` a draft implements."
  [definition interfaces methods]
  (when-not (and (map? definition) (or (nil? interfaces) (sequential? interfaces))
                 (or (nil? methods) (map? methods)) (every? class? interfaces))
    (refuse :malformed "not {:interfaces [class ...] :methods {signature f}}" (without-functions definition)))
  (let [ks (:keys definition)]
    (when-not (or (nil? ks)
                  (and (sequential? ks) (every? keyword? ks) (= (count ks) (count (distinct ks)))))
      (refuse :malformed "the keys are distinct keywords" ks))
    (when (> (count ks) max-keys)
      (refuse :too-many-keys (str "a definition declares at most " max-keys " keys") (count ks))))
  (when-not (contains? #{nil true false} (:unsealed definition))
    (refuse :malformed ":unsealed is true or false" (:unsealed definition)))
  (doseq [^Class i interfaces
          :when (and (not= Object i) (some #(.isAssignableFrom i %) draft-interfaces))]
    (refuse :draft-interface "a draft implements this interface, and a draft implements none of its definition's" i
            :interfaces [i])))

(defn- by-signature
  "One Method for each [name params] of `listed`, the members of the listed interfaces by
  [name params]. Refuses two that differ only in return type, among the methods T does not
  have as a map."
  [listed]
  (into {} (for [[k pairs] listed
                 :let [ms (distinct (map second pairs))]]
             (do (when (and (not (apply implemented? k))
                            (< 1 (count (distinct (map #(.getReturnType ^Method %) ms)))))
                   (refuse :clash "two listed methods differ only in return type" k
                           :method (apply method-of k)
                           :interfaces (vec (distinct (map #(.getDeclaringClass ^Method %) ms)))))
                 [k (first ms)]))))

(defn- resolve-signature
  "The [name params] of `by-sig` that the signature `sig`, [name arity] or [name [class ...]],
  names. Refuses a malformed signature, `equals` and `hashCode`, a signature that no method or
  more than one matches, and one that names a method T has without the definition."
  [by-sig [nm spec :as sig]]
  (when-not (and (vector? sig) (= 2 (count sig)) (or (symbol? nm) (string? nm))
                 (or (nat-int? spec) (and (vector? spec) (every? class? spec))))
    (refuse :malformed "a signature is [name arity] or [name [class ...]]" sig))
  (let [n (str nm)]
    (when (#{"equals" "hashCode"} n)
      (refuse :equality "a value's equality is its map's" sig :method (sig-method sig)))
    (let [found (filter (fn [[[mn ps]]]
                          (and (= n mn) (if (vector? spec) (= spec ps) (= spec (count ps)))))
                        by-sig)]
      (case (count found)
        0 (refuse :undeclared "no listed interface declares" sig :method (sig-method sig))
        1 (let [[k] (first found)]
            (when (and (apply implemented? k) (not= k ["toString" []]))
              (refuse :map-method "a value has this method without the definition" sig
                      :method (sig-method sig)))
            k)
        (refuse :ambiguous "more than one method matches" sig :method (sig-method sig))))))

(defn- given-methods
  "The definition's `methods`, {signature f}, as {[name params] f}. Refuses an f that is
  neither nil nor `ifn?`, and two signatures of one method."
  [by-sig methods]
  (reduce (fn [acc [sig f]]
            (let [k (resolve-signature by-sig sig)]
              (when-not (or (nil? f) (ifn? f))
                (refuse :not-a-function "not a function" sig :method (sig-method sig)))
              (when (contains? acc k)
                (refuse :duplicate "two signatures name one method" sig :method (sig-method sig)))
              (assoc acc k f)))
          {} methods))

(defn- default-bodies
  "The default bodies a call of `k`, a [name params] of `listed`, could run, where no class T
  extends declares it."
  [listed k]
  (if (apply class-implemented? k)
    []
    (filter #(.isDefault ^Method %)
            (maximal (distinct (map second (concat (listed k) (map-methods k))))))))

(defn- refuse-default-clashes!
  "Refuses a method of `by-sig` that the definition gives no function in `given` and whose
  most specific declarations give more than one default body."
  [listed by-sig given]
  (doseq [k (keys by-sig)
          :when (not (contains? given k))
          :let [ds (default-bodies listed k)]
          :when (< 1 (count ds))]
    (refuse :clash
            (str "the interfaces " (str/join " and " (map #(.getName (.getDeclaringClass ^Method %)) ds))
                 " give default bodies of " (first k) " and the definition gives no function for it")
            k
            :method (apply method-of k)
            :interfaces (vec (map #(.getDeclaringClass ^Method %) ds)))))

(defn- plan
  "The methods of `definition` that T forwards, as [interfaces plan]: each entry of the plan
  is {:name :params :ret :f}, `:f` nil where no function implements the method. Besides the
  refusals of the definition's shape, refuses:

  - a signature that no listed interface declares, that matches more than one method, or that
    names a method T has without the definition;
  - two signatures of one method;
  - `equals` and `hashCode`;
  - two listed methods of one name and parameters with different return types, among the
    methods T does not have as a map;
  - a method with no function whose most specific declarations give more than one default
    body.

  A method with no function and no default body among its most specific declarations
  forwards to nothing, and throws; one with exactly one default body keeps that body."
  [{:keys [interfaces methods] :as definition}]
  (check-shape! definition interfaces methods)
  (let [listed  (group-by first (mapcat members (distinct interfaces)))
        by-sig  (by-signature listed)
        given   (given-methods by-sig methods)
        _       (refuse-default-clashes! listed by-sig given)
        sigs    (distinct (concat (for [k (keys by-sig)
                                        :when (and (not (apply implemented? k)) (empty? (default-bodies listed k)))]
                                    k)
                                  (keys given)))]
    [(vec (remove #(= Object %) (distinct interfaces)))
     (vec (for [[n ps :as k] sigs
                :let [^Method m (by-sig k)]]
            {:name n :params ps :ret (.getReturnType m) :f (given k)}))]))

(defn- print-preferences
  "Where `print-method` or `print-dup` has an entry for a listed interface or one of its
  supertypes, the preferences of the map's entry, and of `Proven`'s, over that entry, as
  [multimethod-name multimethod winner entry]. Without them, a value, which is both a map and
  an instance of the interface, would match two entries, and printing it would throw."
  [ifaces]
  (for [[nm ^MultiFn mf] [["print-method" print-method] ["print-dup" print-dup]]
        k (keys (methods mf))
        :when (and (class? k) (not= Object k) (not (isa? clojure.lang.IPersistentMap k))
                   (some #(isa? % k) ifaces))
        winner [clojure.lang.IPersistentMap recognitum.proof.Proven]]
    [nm mf winner k]))

(defn outranked
  "The refusal where multimethod `nm` already prefers interface `k`'s entry to the map's."
  [nm k]
  (refusal-of :clash (str nm " prefers this interface's entry to the map's, so a value could not print as its map") k
              {:interfaces [k]}))

(defn- check-outranked
  "Refuses where one of `prefs` cannot be set because the entry is already preferred over the
  winner. Tried on a copy of each multimethod's preferences, so it changes none."
  [prefs]
  (doseq [[nm group] (group-by first prefs)
          :let [^MultiFn mf (second (first group))
                copy (MultiFn. nm (.-dispatchFn mf) (.-defaultDispatchVal mf) (.-hierarchy mf))]]
    (doseq [[x ys] (.getPreferTable mf), y ys] (.preferMethod copy x y))
    (doseq [[_ _ winner k] group]
      (try (.preferMethod copy winner k)
           (catch IllegalStateException _ (throw (ex-info "refused" {:recognitum.proof.key-class/refusal (outranked nm k)})))))))

(defn analysis
  "What defining `definition` takes, `{:interfaces :plan :prefs :keys :unsealed :instead}`,
  or why it is refused, `{:refusal r}`. Defines and sets nothing. Besides [[plan]]'s refusals,
  refuses:

  - a listed interface whose name now loads another class (an interface defined again after
    the definition named it), which would leave the values outside the interface listed;
  - a print preference that cannot be set;
  - an `:instead` that is neither a string nor nil, or is longer than [[max-words]]."
  [definition]
  (try
    (let [[ifaces plan] (plan (or definition {}))
          instead (:instead definition)
          loader (DynamicClassLoader. (RT/baseLoader))]
      (when-not (or (nil? instead) (string? instead))
        (refuse :malformed ":instead is a string or nil" instead))
      (when (> (count instead) max-words)
        (refuse :too-many-words (str ":instead holds at most " max-words " characters") (count instead)))
      (doseq [^Class i ifaces]
        (when-not (identical? i (try (Class/forName (.getName i) false loader)
                                     (catch ClassNotFoundException _ nil)))
          (refuse :reloaded-interface "the interface's name now names another class" i :interfaces [i])))
      (let [prefs (print-preferences ifaces)]
        (check-outranked prefs)
        {:interfaces ifaces :plan plan :prefs prefs :keys (vec (:keys definition))
         :unsealed (true? (:unsealed definition)) :instead instead}))
    (catch clojure.lang.ExceptionInfo e
      (if-let [r (:recognitum.proof.key-class/refusal (ex-data e))] {:refusal r} (throw e)))))

(defn refusal
  "Nil where `recognitum.proof.key-class` accepts `definition`, else the refusal that defining
  it throws."
  [definition]
  (:refusal (analysis definition)))
