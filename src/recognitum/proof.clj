(ns recognitum.proof
  "The protocol between the record layer and a proof strategy. A strategy defines types. Each
  definition of a type returns a handle: an opaque object that holds the type's access key.
  Every function that needs the access key takes the handle. A caller keeps the handle in a
  closure, never in a var, so that no var holds an access key.

  What every strategy guarantees:

  - a value is proven under a handle only if `seal` made it with that handle, or the write
    installed on that handle accepted it, or a guard installed with that write returned for
    an `assoc` of the guard's key, or a change guard installed with that write returned for
    a change;
  - on a proven value, each change (one `assoc` or `dissoc` of one key, one `conj`, `merge`
    of one map, or one `into`) makes one call: of the guard of its key, where the change is an
    `assoc` of a key that has one; else of the change guard, where one is installed; else of
    the installed write. `conj` of one entry may instead call what an `assoc` of that entry
    calls. The write is given the whole map that the change makes, and for `assoc` and
    `dissoc` also the key; a guard or a change guard is given only the entries that the
    change alters. An `assoc` or a `dissoc` that alters nothing may return the value itself
    without calling the write; with a change guard, a change that alters nothing calls
    nothing and returns the value itself. `empty` throws, as on a `defrecord`;
  - with no write installed, every change that alters a value gives a map that is proven
    under no handle;
  - a value keeps one field per key that its definition declares, and answers as the plain
    map of its entries;
  - `define-type` again with the same name is a redefinition: values of the earlier
    definition are not proven under the new handle, and keep their definition's methods;
  - a definition's value class and draft class each have a public static method `gate()`,
    which takes nothing and returns the `clojure.lang.IFn` that `installed` returns, so the
    class answers for its definition without any table; [[gate-of]] calls it;
  - a definition's value class implements [[Proven]], an interface with no methods, so one
    entry in a multimethod such as `print-method` serves the values of every definition;
  - a value prints as its map: the text shows its data alone and never reads back proven;
  - a definition may be unsealed. `proven?` is false of its values under every handle, and
    none of them is an instance of a sealed definition's value class. Its handle seals
    nothing and installs no write. With the access key, the handle builds values that hold a
    memory, which [[memory]] reads without the access key, and installs a carry, which every
    change of such a value calls.

  Not guaranteed: that `with-meta` keeps proof. `seal` takes the metadata of the map it seals,
  so a caller sets the metadata before sealing.

  Never reload this namespace. A reload makes new protocols and interfaces under the old
  names, and every existing handle and value implements only the old ones.")

(definterface Proven)

(definterface Built
  (^Object memory$ []))

(defprotocol Strategy
  (define-type [strategy type-name] [strategy type-name definition]
    "Defines a type: a new class for its values, a new class for its drafts, and a new access
    key. Returns the handle. `definition` is a map:

    - `:keys`, `[k ...]`: the keys of the type's fields, distinct keywords. A value keeps one
      field per declared key, so `get` of one reads a field, and keeps its other entries in a
      map. A value may lack a declared key or hold nil under it, and answers as the plain map
      of its entries.
    - `:interfaces`, `[class ...]`: the interfaces that every value of the type implements. A
      draft implements none of them. `Object` may be listed, so that `:methods` may give
      `toString`, the one method of `Object` that a definition may give.
    - `:methods`, `{signature f}`: the functions behind the methods. A signature is
      `[name arity]`, the arity counting the arguments after the value, or
      `[name [class ...]]`, the parameter types. `f` takes the value and then the method's
      arguments. An abstract method with no `f` throws when called; a default method with no
      `f` keeps its body.
    - `:unsealed true` makes the definition unsealed: its handle `build`s values and seals
      none (see [[Handle]]). The rest of the definition means what it means without the flag.
    - `:instead`, a string: what a caller should do in place of calling the class's
      constructor. Called without the access key, the constructor throws with a message that
      names the class and closes with these words, or with the strategy's own where
      `:instead` is nil or absent. The class keeps its words after the type is redefined.

    Without a definition, the values implement no interface of their own. Where [[refusal]]
    answers a refusal of `definition`, throws `ex-info` with that refusal as its data and its
    `:message` as its message, and defines nothing.")
  (refusal [strategy definition]
    "Nil where `define-type` accepts `definition`, else the refusal that it would throw: a map
    with `:kind` and `:message` and, as the kind requires, one or both of these:

    - `:method`, `[name arity]`: the name as the signature spells it, as a symbol, neither
      munged nor demunged, and the arity counting the arguments after the value;
    - `:interfaces`, `[class ...]`.

    Every strategy refuses:

    - a signature that names a method no listed interface declares (`:undeclared`);
    - an `[name arity]` that matches more than one method (`:ambiguous`);
    - `equals` or `hashCode` (`:equality`).

    A strategy may also refuse `:keys` that are not distinct keywords, a method that the value
    has as a map (`:map-method`), a clash of the listed interfaces with each other or with the
    map's, by default bodies, return types or print entries (`:clash`), and more, under kinds
    of its own.

    Needs no access key and defines nothing. The answer depends on `definition`, on the
    classes that the names of the listed interfaces load, and on the entries of `print-method`
    and `print-dup`, as they are at the call. `:unsealed` true or false changes no answer. An
    `:instead` that is neither a string nor nil is refused, and so may be one too long to
    hold.")
  (class-name [strategy type-name]
    "The name of the class of the values of the type named `type-name`, a qualified symbol,
    the same under every definition of the type: `my.ns/T` -> `my.ns.T`. Nil for a nil
    `type-name`, whose class name each definition makes anew.")
  (marked? [strategy draft check]
    "Whether `draft` is a draft that this strategy's `open` made and on which `check`, compared
    by `=`, is marked as passed: what `passed?` answers of the draft under the handle that
    opened it, also after the type is redefined. False for anything else. Needs no access key
    and changes nothing.")
  (installed [strategy value-class]
    "A function that calls the write installed on the definition whose values are of
    `value-class`, or nil where none is installed. Neither this call nor the function needs
    the access key. The function's arities:

    - one or two arguments: throws where the first, `old`, is not a value of that definition;
    - three arguments: passes them to the write as they are.

    It has no four-argument arity. Of an unsealed definition, it has the three-argument arity
    alone.")
  (memory [strategy v]
    "The memory that `v` holds, the very object that `build` or the carry gave it, where `v` is
    a value of an unsealed definition of this strategy; nil for anything else. Needs no access
    key, and reads, calls and changes nothing in the memory.")
  (removed [strategy]
    "The marker of a removed key: what the four-argument arity of an installed write gets as
    `v` where a `dissoc` removes `k`, and what a change guard's or a carry's `changes` maps a
    removed key to. One object for every type of the strategy, which no value holds."))

(defprotocol Handle
  (seal [h m]
    "A value of the type that holds `m`'s entries and metadata, proven under `h`. Throws,
    making nothing, where `h` is unsealed.")
  (build [h m mem]
    "A value of the type that holds `m`'s entries and metadata and the memory `mem`. No check
    runs, and the value is proven under no handle. Throws, making nothing, where `h` is not
    unsealed.")
  (proven? [h v]
    "Whether `v` is proven under `h`. A value of any other definition of the type is not.
    False under an unsealed `h`.")
  (install-write! [h write] [h write key-write] [h write key-write change-guard]
    "Installs `write` as the write of every value of the type, with or without `key-write` and
    `change-guard`. Installs once per handle: a second call throws or does nothing. Throws,
    installing nothing, where `h` is unsealed.

    `write` returns a sealed value or throws. Its arities:

    - `(write old entries)`, called by `conj`, `merge` and `into`, `entries` being the whole
      map that the change makes;
    - `(write old entries k v)`, called by `assoc` of `k` to `v` and by `dissoc` of `k`,
      `entries` again being the whole map, and `v` being the strategy's [[removed]] for a
      `dissoc`;
    - a three-argument arity, which a caller without the access key reaches through
      `installed`.

    `conj` of one entry may call either of the first two. The first two arities must answer
    alike for the same `old` and `entries`.

    With `key-write`, the strategy calls `(key-write k)` with declared keys only, each at most
    once. It answers nil or a guard `(g old v)`, a function made by `fn` (`fn?`). A keyword, a
    map, a set or a var returns for any argument, and so would permit every write: an install
    that gets one throws and installs nothing. Where `k` has a guard, `assoc` of `k`, on a
    value proven under `h`, to a `v` that is not the value's entry under `k`, calls
    `(g old v)` and not `write`:

    - where `g` returns, whatever it returns, `assoc` returns a value proven under `h` that
      holds `old`'s entries and metadata with `k` set to `v`;
    - where `g` throws, the throw propagates and nothing is made.

    Without a change guard, `assoc` of other keys, `dissoc`, `conj`, `merge` and `into` call
    `write`, except that `conj` of one entry may call the guard of its key instead. `g` must
    answer as `write` would for `old` and its entries with `k` set to `v`: it returns where
    `write` would return a value, and throws what `write` would throw. Nothing reaches a guard
    through `installed`.

    With `change-guard`, `(cg old changes)`, also made by `fn`: `changes` maps each key whose
    entry a change alters to its new value, or to [[removed]] where the change removes the
    key. A value identical to `old`'s entry, or a removal of a key that `old` lacks, is no
    change. On a value proven under `h`, `conj`, `merge`, `into` (a transient's
    `persistent!`), `dissoc`, and `assoc` of a key with no guard call `(cg old changes)` once
    and do not call `write`, except that `conj` of one entry may call the guard of its key
    instead:

    - where `changes` would be empty, they call nothing and return `old`;
    - where `cg` returns, the change returns a value proven under `h` that holds `old`'s
      entries with `changes` applied, and `old`'s metadata;
    - where `cg` throws, the throw propagates.

    `cg` must answer as `write` would for `old` and those entries. Nothing reaches it through
    `installed`.")
  (install-carry! [h write carry]
    "On an unsealed `h`, installs `write` and `carry`, once, and with no other install.
    `installed` reaches only the three-argument arity of `write`. `carry`, `(carry old
    changes)`, is made by `fn`. `assoc`, `dissoc`, `conj`, `merge` and `into` (a transient's
    `persistent!`) of a value of `h` call `(carry old changes)` once, `changes` being the net
    change, as [[install-write!]] describes it for a change guard:

    - where `changes` would be empty, they call nothing and return `old`;
    - where `carry` returns `m`, the change returns a value of `h` that holds `old`'s entries
      with `changes` applied, `old`'s metadata, and the memory `m`;
    - where `carry` throws, the throw propagates.

    Throws, installing nothing, where `h` is not unsealed, or on a second call.")
  (open [h]
    "A new draft of the type, with no marks.")
  (mark! [h draft check]
    "Marks `check` as passed on `draft`.")
  (passed? [h draft check]
    "Whether `check` is marked as passed on `draft`.")
  (classes [h]
    "`[value-class draft-class]`: the class of every value proven under `h`, and of every draft
    `open` returns. Holding them grants nothing: the access key stays in `h`.")
  (capabilities [h]
    "The objects that hold the access key, so that a test can confirm that no loaded var holds
    one."))

(defn checked-transient
  "For strategies: a transient over `old`'s entries whose `persistent!` makes one call
  `(write old entries)`, `entries` being the transient's entries at that point, so that `into`
  is one checked write however many entries it adds."
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
  "For strategies: `m`'s entries and metadata as a plain persistent map. Reads `m` only
  through its seq or its iterator, so that no protocol caches `m`'s class: a cache entry would
  keep a type's class loaded."
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
