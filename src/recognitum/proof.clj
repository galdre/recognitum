(ns recognitum.proof
  "The proof protocol. A strategy defines types; each
  definition is an opaque handle that holds the type's key. Every keyed op takes the handle,
  so the caller keeps the key only by keeping the handle in a closure, never in a var.

  What every strategy guarantees:
  - a value is proven under a handle only if `seal` made it with that handle, or the write
    installed on that handle accepted it, or a guard installed with that write returned for
    an `assoc` of its key, or a change guard installed with it returned for a change;
  - `clojure.core` `assoc`, `dissoc`, `conj`, `merge` and `into` on a value proven now go
    through the installed write, if there is one. Each is one write, given the whole result;
    `assoc` and `dissoc` also name the key they write. With a change guard, each is one call
    of the guard of its key or of the change guard, given only the entries it changes.
    `empty` throws, as on a `defrecord`;
  - a value keeps one field per key its definition declares, and answers as the plain map of
    its entries;
  - with no write installed, every change yields an unproven map;
  - `define-type` again with the same name is redefinition: values of the earlier
    definition are not proven under the new handle;
  - a definition's value class and draft class each have a public static method `gate()`,
    taking nothing and returning the `clojure.lang.IFn` that `installed` returns, so the
    class answers for its definition without any table; [[gate-of]] calls it;
  - a definition's value class implements [[Proven]], an interface with no methods, so one
    entry in a multimethod such as `print-method` serves the values of every definition;
  - a value keeps its definition's methods after a redefinition;
  - a value prints as its map: the text shows its data alone and never reads back proven;
  - a definition may be unsealed: `proven?` is false of its values under every handle, none
    of them is an instance of a sealed definition's value class, and its handle seals and
    installs no write; with the key it builds values that hold a memory, which [[memory]]
    reads without it, and installs a carry that every change of a value calls.

  Not guaranteed: that `with-meta` keeps proof. `seal` takes the meta of the map it seals,
  so a caller sets meta before sealing.

  This namespace is never reloaded: reloading it would orphan every handle.")

(definterface Proven)

(definterface Built
  (^Object memory$ []))

(defprotocol Strategy
  (define-type [strategy type-name] [strategy type-name definition]
    "Evaluates a type's definition: a new type and its key. Returns the handle.
    `definition`, `{:keys [k ...] :interfaces [class ...] :methods {signature f}}`, names the
    keys of the type's fields, distinct keywords, the interfaces every value of the type
    implements and the functions behind their methods. A value keeps one field per declared
    key, so `get` of one reads a field, and its other entries in a map; it may lack a declared
    key or hold nil under it, and answers as the plain map of its entries. A signature
    is `[name arity]`, the arity counting the arguments after the value, or
    `[name [class ...]]`, the parameter types. `f` takes the value and then the method's
    arguments. Of `Object`, `toString` may be given. An abstract method with no `f` throws
    when called; a default method with no `f` keeps its body; a draft implements none of
    the interfaces. Without a definition, the values implement no interface of their own.
    `:unsealed true` makes the definition unsealed: its handle `build`s values and seals
    none (see [[Handle]]); the rest of the definition means what it means without the flag.
    Where [[refusal]] answers a refusal of `definition`, throws `ex-info` with that refusal
    as its data and its `:message` as its message, and defines nothing.")
  (refusal [strategy definition]
    "Nil where `define-type` accepts `definition`, else the refusal it would make: a map with
    `:kind`, `:message`, and, by kind, `:method`, `[name arity]` with the name the signature's
    own spelling as a symbol, neither munged nor demunged, and the arity counting the
    arguments after the value, or `:interfaces`, `[class ...]`. Every strategy refuses a
    signature that names a method no listed interface declares (`:undeclared`), an
    `[name arity]` that matches more than one method (`:ambiguous`), and `equals` or
    `hashCode` (`:equality`). It may refuse `:keys` that are not distinct keywords, a method
    the value has as a map (`:map-method`), a clash of listed interfaces with each other or
    with the map's, by default bodies, return types or print entries (`:clash`), and more,
    under kinds of its own. Needs no key and defines nothing. The answer depends on
    `definition`, on the classes the listed interfaces' names load, and on the print
    entries, as they are when called. `:unsealed` changes no answer.")
  (class-name [strategy type-name]
    "The name of the class of the values of the type named `type-name`, a qualified symbol,
    the same under every definition of the type: `my.ns/T` -> `my.ns.T`. Nil for a nil
    `type-name`, whose class name each definition makes anew.")
  (marked? [strategy draft check]
    "Whether `draft` is a draft that this strategy's `open` made and that records `check`,
    compared by `=`, as passed: what `passed?` answers of it under the handle that opened it,
    also after the type is redefined. False for anything else. Needs no key and changes
    nothing.")
  (installed [strategy value-class]
    "A function that calls the write installed on the definition whose values are of
    `value-class`, or nil when none is installed. It needs no key. Called with one or two
    arguments, it refuses an `old` that is not a value of that definition; called with three,
    it passes them to the write as they are. It has no four-argument arity. Of an unsealed
    definition it has the three-argument arity alone.")
  (memory [strategy v]
    "The memory `v` was built or carried with, the very object, where `v` is a value of an
    unsealed definition of this strategy; nil for anything else. Needs no key, and reads,
    calls and changes nothing in the memory.")
  (removed [strategy]
    "The object the four-argument arity of an installed write gets as `v` where a `dissoc`
    removes `k`: one object for every type of the strategy, which no value holds."))

(defprotocol Handle
  (seal [h m]
    "A value of the type holding `m`'s entries and meta, proven under `h`. Throws, making
    nothing, where `h` is unsealed.")
  (build [h m mem]
    "A value of the type holding `m`'s entries and meta and the memory `mem`, which no check
    ran on and which is proven under no handle. Throws, making nothing, where `h` is not
    unsealed.")
  (proven? [h v]
    "Whether `v` is proven under `h`, the type's current definition. False under an unsealed
    `h`.")
  (install-write! [h write] [h write key-write] [h write key-write change-guard]
    "Installs `write` as the write of every value of the type. Once per handle, with or
    without `key-write` and `change-guard`: a second call throws or does nothing. `write`
    returns a sealed value or throws. `(write old entries)` is called by `conj`, `merge` and
    `into`, `entries` the whole map the change makes; `(write old entries k v)` by `assoc` of
    `k` to `v` and `dissoc` of `k`, `entries` the whole map again and `v` the strategy's
    [[removed]] for a `dissoc`. The two answer alike of the same `old` and `entries`. A three-argument arity of
    `write` is reachable, without the key, through `installed`.

    With `key-write`, the strategy calls `(key-write k)` with declared keys only, each at
    most once; it answers nil or a guard `(g old v)`, a function made by `fn` (`fn?`): a
    keyword, a map, a set or a var returns for any argument, and so would permit every write,
    and an install that gets one throws and installs nothing. Where `k` has a guard, `assoc` of `k` to
    a `v` that is not the value's entry under `k`, on a value proven under `h`, calls
    `(g old v)` and not `write`: where `g` returns, whatever it returns, `assoc` returns a
    value proven under `h` holding `old`'s entries and meta with `k` set to `v`; where it
    throws, the throw propagates and nothing is made. Other keys, `dissoc`, `merge` and `into`
    call `write`. `g` answers as `write` would of `old` and its entries with `k` set to `v`:
    it returns where `write` would return a value and throws what `write` would throw.
    Nothing reaches a guard through `installed`.

    With `change-guard`, `(cg old changes)`, also made by `fn`: `changes` maps each key whose
    entry a change alters to its new value, or to [[removed]] where the change removes it;
    a value identical to `old`'s entry, or a removal of a key `old` lacks, is no change. On
    a value proven under `h`, `conj`, `merge`, `into` (a transient's `persistent!`),
    `dissoc`, and `assoc` of a key with no guard call `(cg old changes)` once and not
    `write`. Where `changes` would be empty they call nothing and return `old`. Where `cg`
    returns, the change returns a value proven under `h` holding `old`'s entries with
    `changes` applied and `old`'s meta; where it throws, the throw propagates. `cg` answers
    as `write` would of `old` and those entries. Its cost is in proportion to the entries
    the change names. Nothing reaches it through `installed`.

    Throws, installing nothing, where `h` is unsealed.")
  (install-carry! [h write carry]
    "On an unsealed `h`, once, with no other install: `write`, of which `installed` reaches
    the three-argument arity alone, and `carry`, `(carry old changes)`, made by `fn`.
    `assoc`, `dissoc`, `conj`, `merge` and `into` (a transient's `persistent!`) of a value of
    `h` call `(carry old changes)` once, `changes` the net change as a change guard is told
    it. Where `changes` would be empty they call nothing and return `old`; where `carry`
    returns `m`, the change returns a value of `h` holding `old`'s entries with `changes`
    applied, `old`'s meta and the memory `m`; where it throws, the throw propagates. Throws,
    installing nothing, where `h` is not unsealed, or a second time.")
  (open [h]
    "A new draft of the type, with no marks.")
  (mark! [h draft check]
    "Marks `check` passed on `draft`.")
  (passed? [h draft check]
    "Whether `check` is marked passed on `draft`.")
  (classes [h]
    "`[value-class draft-class]`: the class of every value proven under `h`, and of every draft
    `open` returns. Holding them grants nothing: the key stays in `h`.")
  (capabilities [h]
    "The objects that hold the key, so that a test can confirm no loaded var holds one."))

(defn checked-transient
  "For strategies: a transient over `old`'s entries whose persistent! makes one call
  `(write old entries)`, so `into` is one checked write however many entries it adds."
  [old write]
  (let [t    (volatile! (transient (into {} (seq old))))
        done (volatile! false)
        live (fn [] (when @done (throw (IllegalAccessError. "Transient used after persistent! call"))) @t)]
    (reify
      clojure.lang.ITransientMap
      (assoc [this k v] (vreset! t (assoc! (live) k v)) this)
      (without [this k] (vreset! t (dissoc! (live) k)) this)
      (conj [this o] (vreset! t (conj! (live) o)) this)
      (persistent [_] (let [r (persistent! (live))] (vreset! done true) (write old r)))
      (count [_] (count (live)))
      (valAt [_ k] (get (live) k))
      (valAt [_ k nf] (get (live) k nf))
      clojure.lang.ITransientAssociative2
      (containsKey [_ k] (contains? (live) k))
      (entryAt [_ k] (when (contains? (live) k) (clojure.lang.MapEntry/create k (get (live) k)))))))

(defn plain-map
  "For strategies: `m`'s entries and meta as a plain persistent map. Reads `m` through its
  seq, or, for a map of at most eight entries, its iterator, so no protocol caches `m`'s
  class: a cache entry would keep a type's class loaded."
  [m]
  (cond (or (instance? clojure.lang.PersistentArrayMap m) (instance? clojure.lang.PersistentHashMap m))
        m
        ;; as `into {}` makes it, in the same order: an array map up to eight entries
        (and (instance? clojure.lang.IPersistentMap m) (<= (count m) 8))
        (let [a (object-array (* 2 (count m)))
              it (.iterator ^Iterable m)]
          (loop [i 0]
            (when (.hasNext it)
              (let [^java.util.Map$Entry e (.next it)]
                (aset a i (.getKey e))
                (aset a (inc i) (.getValue e))
                (recur (+ i 2)))))
          (clojure.lang.PersistentArrayMap. (meta m) a))
        :else
        (with-meta (into {} (seq m)) (meta m))))

(defonce ^:private gate-methods
  (proxy [java.lang.ClassValue] []
    (computeValue [^Class c]
      (try (let [m (.getMethod c "gate" (make-array Class 0))]
             (when (and (java.lang.reflect.Modifier/isStatic (.getModifiers m))
                        (= clojure.lang.IFn (.getReturnType m)))
               m))
           (catch NoSuchMethodException _ nil)))))

(defn gate-of
  "The function `installed` returns for the definition whose value class or draft class is
  `c`, found by calling the class's static `gate()`. Nil for any other class, and for a
  definition with no write installed. The lookup of each class's method is cached on the
  class, so it leaves nothing behind that would keep the class loaded."
  [^Class c]
  (when-let [^java.lang.reflect.Method m (.get ^java.lang.ClassValue gate-methods c)]
    (.invoke m nil (object-array 0))))
