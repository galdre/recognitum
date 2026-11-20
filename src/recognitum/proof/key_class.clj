(ns recognitum.proof.key-class
  "The key-class proof strategy: each definition of a type emits a final APersistentMap
  subclass T whose one public constructor needs T's key, and a draft class T$Draft whose
  mark needs it too. The handle `define-type` returns holds the key; this namespace holds
  none, so reloading it loses nothing and strands nothing.

    T  extends APersistentMap implements IObj, IEditableCollection, IMapIterable,
       recognitum.proof.Proven and each interface its definition lists; where the definition declares keys, also
       IKeywordLookup. final. Holds one field f<i> per declared key K<i>, ABSENT where the
       value lacks that key, a private map `ext` of its other entries, a private `_meta`
       and a private count `cnt`, which every constructor sets. T(Object key, Object data) throws unless key is T.KEY, a
       SecurityException whose message, one constant, names T and closes with the words the
       definition handed down as `:instead`, or with the strategy's own; it splits data into the
       fields and ext, and takes data's meta. Reads of a declared key read its field, others
       forward to ext; a keyword's lookup of a declared key reads the field through a thunk
       class T$K<i>, as on a defrecord. seq conses the present fields' entries, in the order
       of the keys, onto ext's seq; iterator, keyIterator and valIterator are a T$I, which
       walks the same entries reading the fields; equiv and equals against
       another T compare field by field, then ext. Private static volatiles WRITES, GATE, CHG
       and, per declared key, G<i> are set once, with the key, by install(key, writes, gate,
       guards, changes): while
       WRITES is set, assoc and without return WRITES.invoke(this, entries, k, v), v the
       strategy's marker for a removed key on without, and assocEx and cons return
       WRITES.invoke(this, entries), entries the whole new map, each one checked write that
       seals or throws; asTransient returns WRITES.invoke(this), a transient whose
       persistent! makes one checked write (into). Where G<i> is set, an assoc of K<i> to a
       v not identical to f<i> calls G<i>.invoke(this, v) in place of WRITES, and where that
       returns, returns a T made by a private constructor from this with f<i> set to v; the
       guard is handed no way to make a value. Where CHG is set, every other assoc, and
       without and cons, call CHG.invoke(this, ...) in place of WRITES: it answers the net
       change as flat pairs after the change guard returned, or null where nothing changes,
       and the change returns a T made by a private constructor from this and those pairs,
       or this. asTransient then returns CHG.invoke(this), a transient whose persistent! is
       one cons of what it was told. CHG holds no key. While WRITES is not set, every other change
       returns a plain map. A public static gate() returns
       GATE, which needs no key to call and has no four-argument arity. A no-op assoc,
       without or cons returns this. empty throws, as on a defrecord. withMeta with the same
       meta returns this. writeReplace serializes a plain map; readObject throws. A static
       create(IPersistentMap) returns its argument, so #T{...} reads back as a plain map.
       Each method the definition gives a function, `toString` included, and each
       abstract method of a listed interface that T does not already have, is a
       forwarding method: it calls the function in a private static FNS table, set once by
       claim(fns, removed) when the type is defined, with the value itself and the call's arguments,
       boxed; a slot with no function throws UnsupportedOperationException. The function
       sees no key. A default method with no function keeps its body; two default bodies
       of one method, from interfaces neither of which extends the other, and no function,
       refuse the definition.
    T$Draft implements BiConsumer (accept(key, check): mark) and Predicate (test(check):
       passed?), and none of the listed interfaces: a definition may not list either, nor an
       interface they extend. accept throws unless key is T.KEY. A
       public static gate() returns T.gate(). `define` records on the class, through a
       ClassValue, that it made it, so the keyless `marked?` answers test(check) of its own
       drafts and false of any other object, whatever its class is named.

  An unsealed definition's T differs in these: it also implements recognitum.proof.Built
  and holds a private final `mem`, which memory$() answers; its one public constructor is
  T(Object key, Object data, Object mem); it has no guards and no constructor taking every
  field; a change takes the new value's memory from the last element of what CHG answered,
  after the pairs; assocEx is assoc where the key is absent. Its handle seals nothing and
  proves nothing; install-carry! sets CHG, a WRITES that nothing calls, and a GATE with the
  write's three-argument arity alone. `define` records on the class, through a ClassValue,
  that it made it, so the keyless `memory` answers memory$() of its own values and nil of
  anything else.

  T$New is an AFn whose invoke(key, data) returns new T(key, data), for the handle's seal, or
  of an unsealed T invoke(key, data, mem), for its build; it holds no key. T$I's constructor
  is package-private: only T makes one.

  An assoc of declared key K<i> is a private method assoc$i of its own, which the JIT inlines
  into the call site's assoc; where its guard returns it calls a private constructor taking
  every field, as a defrecord's assoc does. A definition declares at most 250 keys. Past 160,
  a wide T reads a declared key's field through a private field$(i), the index from index$,
  counts its present fields in a private present$(), and walks its fields in chunks, private
  methods reduce$c, kvreduce$c and fill$c, so that no method passes HotSpot's 8000 bytes and
  runs interpreted; a T of at most 160 keys has none of these.

  T.KEY is a package-private static made in <clinit>. claim(fns, removed) hands it out
  once, to `define-type`. Besides recognitum.proof.Proven, defined by a namespace that is never
  reloaded, and the interfaces a definition lists, only JDK and clojure.lang interfaces
  appear in the classes.

  A value prints as its map, so the text shows its data alone, and reads back as a plain
  map; under *print-dup* it prints as T/create of its map, which reads back plain too. Where
  a listed interface or a supertype of it has a `print-method` or `print-dup` entry, the
  definition prefers the map's entry to it, and is refused, with nothing changed, where
  that entry is already preferred to the map's.

  `refusal` and `define-type` refuse through one analysis of the definition: `define-type`
  throws, as `ex-info` data, exactly the refusal `refusal` answers. The kinds beyond the
  protocol's: `:malformed` (the shape of the definition, its keys, its `:instead`, which is a
  string or nil, or a signature), `:too-many-keys` (more than 250 declared keys),
  `:too-many-words` (an `:instead` of more than 10000 characters), `:not-a-function`,
  `:duplicate` (two signatures of one method), `:not-an-interface`, `:draft-interface`
  (an interface a draft implements) and `:reloaded-interface` (a listed interface whose name
  now loads another class)."
  (:require [recognitum.proof :as proof]
            [recognitum.proof.key-class.analysis :refer [analysis outranked refusal]]
            [recognitum.proof.key-class.changes :refer [carry-fn changes-fn removed]]
            [recognitum.proof.key-class.emit :as emit])
  (:import [clojure.lang DynamicClassLoader MultiFn RT]
           [java.lang.reflect Method]))

(set! *warn-on-reflection* true)

(defonce ^:private counter (java.util.concurrent.atomic.AtomicLong.))

(defn fresh-name
  "A new class name, for a new type. Redefinition reuses the name."
  []
  (str "recognitum.proof.key_class.T" (.incrementAndGet ^java.util.concurrent.atomic.AtomicLong counter)))

(defn class-name
  "The class name for `type-name`, a symbol: `my.ns/T` -> `my.ns.T`. Every definition of the
  type names its value class so. Throws for a name that is not a symbol."
  ^String [type-name]
  (when-not (symbol? type-name)
    (throw (IllegalArgumentException. (str "a type's name is a symbol: " (pr-str type-name)))))
  (munge (.replace (str type-name) \/ \.)))

(defn- class-flags
  "One flag per class, false until [[flag!]] sets it, kept on the class itself."
  []
  (proxy [java.lang.ClassValue] []
    (computeValue [_] (java.util.concurrent.atomic.AtomicBoolean.))))

(defn- flag! [^java.lang.ClassValue flags ^Class c]
  (.set ^java.util.concurrent.atomic.AtomicBoolean (.get flags c) true))

(defn- flagged? [^java.lang.ClassValue flags ^Class c]
  (.get ^java.util.concurrent.atomic.AtomicBoolean (.get flags c)))

(defonce ^:private own-drafts
  ;; the draft classes [[define]] made
  (class-flags))

(defonce ^:private own-unsealed
  ;; the value classes of unsealed definitions [[define]] made
  (class-flags))

(defn- marked?
  "Whether `draft` is of a draft class [[define]] made and records `check` as passed."
  [draft check]
  (boolean (and (some? draft)
                (flagged? own-drafts (class draft))
                (.test ^java.util.function.Predicate draft check))))

(defn- memory
  "The memory of `v`, a value of an unsealed definition's class [[define]] made; else nil."
  [v]
  (when (and (instance? recognitum.proof.Built v) (flagged? own-unsealed (class v)))
    (.memory$ ^recognitum.proof.Built v)))

(defn- mark-draft!
  "Marks `check` on `draft`, a draft of the class `dc`, with `key`."
  [^Class dc key draft check]
  (when-not (.isInstance dc draft) (throw (IllegalArgumentException. "not a draft of this type")))
  (.accept ^java.util.function.BiConsumer draft key check)
  nil)

(defn- draft-passed?
  "Whether `draft` is a draft of the class `dc` that records `check`."
  [^Class dc draft check]
  (and (.isInstance dc draft) (.test ^java.util.function.Predicate draft check)))

(defn- install-method
  "The static install of the value class `vc`."
  ^Method [^Class vc]
  (.getMethod vc "install" (into-array Class [Object Object Object (class (object-array 0)) Object])))

(defn- sealing!
  "Refuses an op that seals or installs a write, on an unsealed definition."
  []
  (throw (IllegalStateException. "an unsealed definition seals nothing and takes no write")))

(defn- unsealed-only!
  "Refuses an op of an unsealed definition, on a definition that is not."
  []
  (throw (IllegalStateException. "only an unsealed definition builds a value or takes a carry")))

(defn- unsealed-handle
  "The handle of one emitted class pair of an unsealed definition: it builds values holding a
  memory and proves none. Its write, never called, only marks the install done: with a carry
  installed every change goes through CHG."
  [^Class vc ^Class dc ^clojure.lang.IFn make key]
  (let [draft-ctor (.getConstructor dc (make-array Class 0))
        install    (install-method vc)]
    (reify proof/Handle
      (seal [_ _] (sealing!))
      (build [_ m mem] (.invoke make key (proof/plain-map m) mem))
      (proven? [_ _] false)
      (install-write! [_ _] (sealing!))
      (install-write! [_ _ _] (sealing!))
      (install-write! [_ _ _ _] (sealing!))
      (install-carry! [_ write carry]
        (when-not (fn? carry)
          (throw (IllegalArgumentException. "a carry is made by fn")))
        (.invoke install nil (object-array [key (fn [& _] (sealing!)) (fn [a b c] (write a b c)) nil (carry-fn carry)]))
        nil)
      (open [_] (.newInstance draft-ctor (object-array 0)))
      (mark! [_ draft check] (mark-draft! dc key draft check))
      (passed? [_ draft check] (draft-passed? dc draft check))
      (classes [_] [vc dc])
      (capabilities [_] [key]))))

(defn- handle
  "The handle of one emitted class pair, whose value class declares the keys `ks`. A reify,
  not a map: nothing walks into it."
  [^Class vc ^Class dc ^clojure.lang.IFn make key ks]
  (let [draft-ctor (.getConstructor dc (make-array Class 0))
        install    (install-method vc)
        gate       (.getMethod vc "gate" (make-array Class 0))
        ;; T's changes call the first function, always with the value itself as `old`.
        ;; `installed` hands the second to callers without the key, so a write through it
        ;; starts only from a value of this definition, and it has no four-argument arity: the
        ;; key a caller names is trusted only where T names it. `guards` is nil, or one guard
        ;; or nil per declared key; `changes` nil, or what T's changes call in place of the
        ;; write, which holds no key: T makes the value.
        install!   (fn [write guards changes]
                     (let [own! (fn [old]
                                  (when-not (.isInstance vc old)
                                    (throw (IllegalArgumentException. "a write starts from a value of its type"))))]
                       (.invoke install nil (object-array [key
                                                           (fn
                                                             ([old] (proof/checked-transient old write))
                                                             ([old entries] (write old entries))
                                                             ([old entries k v] (write old entries k v)))
                                                           (fn
                                                             ([old] (own! old) (proof/checked-transient old write))
                                                             ([old entries] (own! old) (write old entries))
                                                             ([a b c] (write a b c)))
                                                           guards
                                                           changes])))
                     nil)
        guards!    (fn [key-write]
                     ;; refused before key-write is asked, so a second install asks nothing
                     (when (.invoke gate nil (object-array 0))
                       (throw (SecurityException. "writes already installed")))
                     (object-array
                      (for [k ks
                            :let [g (key-write k)]]
                        ;; fn?, not ifn?: a guard permits by returning, so a keyword, map,
                        ;; set or var, which returns for any argument, would permit every write
                        (if (or (nil? g) (fn? g))
                          g
                          (throw (IllegalArgumentException. (str "a key write answers nil or a guard made by fn: " (pr-str k))))))))]
    (reify proof/Handle
      (seal [_ m]
        (.invoke make key (proof/plain-map m)))
      (build [_ _ _] (unsealed-only!))
      (proven? [_ v] (.isInstance vc v))
      (install-write! [_ write] (install! write nil nil))
      (install-write! [_ write key-write] (install! write (guards! key-write) nil))
      (install-write! [_ write key-write change-guard]
        (when-not (fn? change-guard)
          (throw (IllegalArgumentException. "a change guard is made by fn")))
        (install! write (guards! key-write) (changes-fn change-guard)))
      (install-carry! [_ _ _] (unsealed-only!))
      (open [_] (.newInstance draft-ctor (object-array 0)))
      (mark! [_ draft check] (mark-draft! dc key draft check))
      (passed? [_ draft check] (draft-passed? dc draft check))
      (classes [_] [vc dc])
      (capabilities [_] [key]))))

(defn- prefer-print-as-map!
  "Sets `prefs`, which [[analysis]] checked. One set meanwhile in the other direction refuses."
  [prefs]
  (doseq [[nm ^MultiFn mf winner k] prefs]
    (try (.preferMethod mf winner k)
         (catch IllegalStateException _
           (let [r (outranked nm k)] (throw (ex-info (:message r) r)))))))

(defn- define
  "Refuses, defining nothing, where [[analysis]] does, throwing the refusal as `ex-info` data
  with its message. The refusal is checked before T is defined, so it leaves no class under
  the type's name."
  [type-name definition]
  (let [{ks :keys :keys [refusal interfaces plan prefs unsealed instead]} (analysis definition)
        _      (when refusal (throw (ex-info (:message refusal) refusal)))
        ^String n (if type-name (class-name type-name) (fresh-name))
        t      (.replace n \. \/)
        d      (str t "$Draft")
        loader (DynamicClassLoader. (RT/baseLoader))
        _      (prefer-print-as-map! prefs)
        vc     (.defineClass loader n (emit/value-class-bytes t interfaces plan ks unsealed instead) nil)
        _      (when unsealed (flag! own-unsealed vc))
        _      (dotimes [i (count ks)]
                 (.defineClass loader (.replace ^String (emit/thunk-name t i) \/ \.) (emit/thunk-bytes t i) nil))
        _      (.defineClass loader (.replace ^String (emit/iter-name t) \/ \.) (emit/iter-bytes t ks) nil)
        dc     (.defineClass loader (.replace d \/ \.) (emit/draft-class-bytes d t) nil)
        _      (flag! own-drafts dc)
        make   (.newInstance (.getConstructor ^Class (.defineClass loader (str n "$New") (emit/maker-bytes t unsealed) nil)
                                              (make-array Class 0))
                             (object-array 0))
        key    (.invoke (.getMethod ^Class vc "claim" (into-array Class [(class (object-array 0)) Object]))
                        nil (object-array [(object-array (map :f plan)) removed]))]
    (if unsealed
      (unsealed-handle vc dc make key)
      (handle vc dc make key ks))))

(def strategy
  "Each `define-type` emits T and T$Draft into a new loader and claims T's key. The same
  name again is redefinition: a new class pair with a new key. A refused definition throws
  and leaves the type as it was: no handle exists for it, and no key is claimed."
  (reify proof/Strategy
    (installed [_ value-class]
      (.invoke (.getMethod ^Class value-class "gate" (make-array Class 0)) nil (object-array 0)))
    (define-type [_ type-name] (define type-name nil))
    (define-type [_ type-name definition] (define type-name definition))
    (refusal [_ definition] (refusal definition))
    (class-name [_ type-name] (when type-name (class-name type-name)))
    (removed [_] removed)
    (marked? [_ draft check] (marked? draft check))
    (memory [_ v] (memory v))))
