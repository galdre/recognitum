# The definition form

`rec/defproven` and `rec/defproven-in` take the same form. This page states everything the form
takes and everything it refuses. Until its [last section](#a-recdefproven-in-type), the page is
about a type that `rec/defproven` defines.

```text
(rec/defproven T [field ...] checks-section ... method-section ...)

field            a plain symbol, or ^:optional and a plain symbol
checks-section   rec/checks clause ...
                 bundle input-clause ...
                 ^{:when-extant field} bundle input-clause ...
clause           (name [wait ...] flags? "docstring"? body ...)
input-clause     (input [] body ...)
flags            a concern | :override | #{flag ...}
method-section   protocol-or-interface method ...
method           (name [this parameter ...] body ...)
```

The example defines one type with every part of the form. The page's other examples use it.

```clojure
(ns bakery.loaf
  (:require [recognitum.core :as rec]))

(rec/defconcern food-safety "What the inspector asks of a loaf.")

(rec/defchecks priced
  "The checks of a price."
  [price]
  rec/checks
  (price-positive [] "the price is above zero" (pos? price))
  (price-in-cents [price-positive] "the price is a whole number of cents" (int? price)))

(defprotocol Describe
  (describe [loaf] "One line about the loaf.")
  (label [loaf] "The text of the loaf's label."))

(rec/defproven Loaf [kind grams ^:optional seeds ^:optional price]
  ^{:when-extant price}
  priced
  (price [] price)

  rec/checks
  (kind  [] "the kind is text" (string? kind))
  (grams [] "the weight is a positive whole number" (pos-int? grams))
  (seeds [] "the seeds are a set" (set? seeds))
  (heavy-enough [] food-safety "a loaf weighs at least 400 g" (<= 400 grams))
  (seeds-are-named [heavy-enough] (rec/when-extant seeds (every? string? seeds)))

  Describe
  (describe [_] (str kind ", " grams " g"))

  Object
  (toString [_] kind))

(def rye (map->Loaf {::kind "rye" ::grams 800}))

(describe rye)
;; => "rye, 800 g"
```

Several examples ask whether a form is refused. A **refusal** is an `ex-info` whose `:error` is
`:recognitum/refused`. Every refusal on this page has that `:error`; the last sections say when
it is thrown and what it leaves.

```clojure
(defn refused?
  "Whether evaluating `form` throws a refusal, as the exception itself or as one of its causes."
  [form]
  (try (eval form) false
       (catch Throwable e
         (boolean (some #(= :recognitum/refused (:error (ex-data %)))
                        (take-while some? (iterate ex-cause e)))))))
```

## What a definition makes

The class `T`, imported into the namespace, and the vars `map->T` and `->T`. A constructor runs
every check, and returns a value or throws. [names.md](names.md) lists every name that a
definition makes, and how another namespace writes each one.

The type's name is a plain symbol. A definition is refused where its name already names a var,
or another class, in the namespace.

```clojure
(def Oven :hot)

(mapv refused?
      '[(rec/defproven bakery/Bun [grams] rec/checks (grams [] (pos-int? grams)))
        (rec/defproven Oven [grams] rec/checks (grams [] (pos-int? grams)))
        (rec/defproven String [grams] rec/checks (grams [] (pos-int? grams)))])
;; => [true true true]
```

## Fields

The fields are a vector of one or more plain symbols, each written once.

- **A field's key** is the keyword in the defining namespace that is named after the field:
  `::grams` for `grams`.
- **A field marked `^:optional` may be absent.** Every other field is **required**: it must be
  present. A field that holds `nil` is present. [absence-and-nil.md](absence-and-nil.md) states
  what each function does where a field is absent.
- **`map->T`** takes a map from field keys to values. **`->T`** takes every field, in order, so
  a `nil` that it is given for an optional field is a present `nil`.
- **A type has at most 250 fields.** A definition with more is refused. `->T` takes every
  field, however many the type has.

```clojure
(mapv refused?
      '[(rec/defproven Bun [] rec/checks)
        (rec/defproven Bun [grams grams] rec/checks)
        (rec/defproven Bun [grams :kind] rec/checks)])
;; => [true true true]

(defn wide
  "A definition form of a type named `tname` with `n` fields and no check."
  [tname n]
  (list 'rec/defproven tname (mapv #(symbol (str "f" %)) (range n))))

[(refused? (wide 'Tray 251)) (refused? (wide 'Tray 250))]
;; => [true false]
```

## Sections

Sections follow the fields: first the checks sections, in any order, then the method sections.
A definition may have no section at all.

A **checks section** is one of two things:

- `rec/checks`, at most once, followed by the type's **own clauses**;
- a bundle's var, followed by the bundle's [binding](#the-binding-of-a-bundle).

A section's head is a symbol. A head that names no bundle, no protocol and no interface is
refused, and so is a clause that stands before any head.

```clojure
(mapv refused?
      '[(rec/defproven Bun [grams] (grams [] (pos-int? grams)))
        (rec/defproven Bun [grams] rec/checks (grams [] true) rec/checks (fresh [] true))
        (rec/defproven Bun [grams] no-such-head (grams [] true))
        (rec/defproven Bun [grams] str (grams [] true))
        (rec/defproven Bun [grams] 42)])
;; => [true true true true true]
```

## A check clause

```text
(name [wait ...] flags? "docstring"? body ...)
```

A clause of `rec/checks` defines a **check**.

- **The name** is a plain symbol, and the check's id is `::name`. Two clauses of one name are
  refused. A check named after a field is that field's **shape check**. The shape check of an
  optional field passes, without running its body, where the field is absent.
- **The waits** are a vector, which may be empty. [Waits](#waits) states what goes in it.
- **The flags** are optional. [Flags](#flags) states what they are and where they go.
- **The docstring** is optional. A string is the docstring only where more forms follow it: a
  string that is the last form of a clause is the body.
- **The body** is one or more forms. The check passes when the body's last form returns exactly
  `true`. Anything else that the body returns is the check's **failure data**, whether or not
  it is truthy.

```clojure
(rec/defproven Crumb [size]
  rec/checks
  (size [] (pos-int? size))
  (truthy [] size)
  (only-a-string [] "this string is the body"))

(try (map->Crumb {::size 3})
     (catch clojure.lang.ExceptionInfo e
       (into {} (for [[id failure] (:failed (ex-data e))] [id (:data failure)]))))
;; => {::truthy 3, ::only-a-string "this string is the body"}

(mapv refused?
      '[(rec/defproven Bun [grams] rec/checks (grams))
        (rec/defproven Bun [grams] rec/checks (grams []))
        (rec/defproven Bun [grams] rec/checks (grams [] true) (grams [] false))])
;; => [true true true]
```

A clause takes no metadata: metadata on a clause, on its name or on its waits is refused.

```clojure
(mapv refused?
      '[(rec/defproven Bun [grams] rec/checks ^:fresh (grams [] true))
        (rec/defproven Bun [grams] rec/checks (^:fresh grams [] true))
        (rec/defproven Bun [grams] rec/checks (grams ^:fresh [] true))])
;; => [true true true]
```

## Waits

A check runs only once every check that it waits on has passed. Where one of them fails, the
check does not run, and a report names it as blocked.

- **A check waits, without being told, on the shape check of each field that its body reads**
  or asks about with `rec/extant?` or `rec/when-extant`, directly or through an input of a
  bundle. The wait vector need not name those shape checks, and naming one changes nothing.
- **The wait vector names every other check that the check waits on:**
  - an own check of the type, by its bare name;
  - a check of a bundle that the type binds, by its var with its namespace:
    `bakery.loaf/price-positive`;
  - every check of such a bundle, by the bundle's var with its namespace: `bakery.loaf/priced`.

The namespace is written even where the bundle is defined in the type's own namespace, because
a bare name in a wait vector names an own check. An alias serves as the namespace.

```clojure
(rec/defproven Roll [grams ^:optional price]
  priced
  (price [] price)

  rec/checks
  (grams [] (pos-int? grams))
  (price [] (number? price))
  (cheap [bakery.loaf/price-positive] (< price 500))
  (sellable [cheap bakery.loaf/priced] true))

(try (map->Roll {::grams "heavy" ::price -1})
     (catch clojure.lang.ExceptionInfo e
       [(set (keys (:failed (ex-data e)))) (:blocked (ex-data e))]))
;; => [#{::grams ::price-positive} #{::price-in-cents ::cheap ::sellable}]
```

Refused in a wait vector:

- a wait that is not a symbol;
- a bare name that names no own check of the type, the bare name of a bundle among them;
- a name with a namespace that names no var, or a var that is neither a bundle nor a check of
  a bundle, or a bundle that the type does not bind, or a check of such a bundle;
- waits that form a cycle, the waits on shape checks among them: two shape checks that read
  each other's fields form one.

```clojure
(mapv refused?
      '[(rec/defproven Bun [grams] rec/checks (grams [:fresh] true))
        (rec/defproven Bun [grams] rec/checks (grams [fresh] true))
        (rec/defproven Bun [grams] priced (price [] grams) rec/checks (grams [priced] true))
        (rec/defproven Bun [grams] rec/checks (grams [bakery.loaf/no-such-var] true))
        (rec/defproven Bun [grams] rec/checks (grams [bakery.loaf/rye] true))
        (rec/defproven Bun [grams] rec/checks (grams [bakery.loaf/priced] true))
        (rec/defproven Bun [grams] rec/checks (grams [bakery.loaf/price-positive] true))
        (rec/defproven Bun [grams] rec/checks (fresh [baked] true) (baked [fresh] true))
        (rec/defproven Bun [grams kind] rec/checks
          (grams [] (some? kind)) (kind [] (some? grams)))])
;; => [true true true true true true true true true]
```

[when-checks-run.md](when-checks-run.md) states which checks each call runs, and in what order.

## Flags

The flags of a clause are the concerns that its check carries, and `:override`.

- **A concern** is a mark that `rec/defconcern` defines. A flag names it by the symbol of its
  var, or by its id, which is the keyword named after that var in the namespace that defined
  it.
- **`:override`** makes the clause replace a check of a bundle that the type binds.
  [The binding of a bundle](#the-binding-of-a-bundle) states the form.

**The flags go right after the waits, before the docstring, and several flags go in one set.**
A keyword, a symbol or a set of them in that place is read as the flags only where more forms
follow it; where it is the last form of the clause, it is the body.

```clojure
(rec/defconcern organic "What the organic label requires.")

(rec/defproven Bagel [grams ^:optional seeds]
  rec/checks
  (grams [] food-safety (pos-int? grams))
  (seeds [] ::organic "the seeds are a set" (set? seeds))
  (seeded [] #{food-safety organic} "a bagel has seeds" (rec/extant? seeds)))

[(rec/checks-of food-safety Bagel) (rec/checks-of organic Bagel)]
;; => [#{::grams ::seeded} #{::seeds ::seeded}]
```

Refused in a clause:

- in the flags' place, a symbol that names no concern;
- in the flags' place, a keyword that is neither `:override` nor a concern's id;
- in the flags' place, a set that holds anything but keywords and symbols, such as `#{42}`;
- a keyword that is a flag, a concern's symbol, or a set that holds either, written later in
  the clause and before the body's last form, where no flag is read: after the docstring, after
  another flag, or among the body's forms;
- a check whose whole body is a concern, since that check has flags and no body.

```clojure
(mapv refused?
      '[(rec/defproven Bun [grams] rec/checks (grams [] str true))
        (rec/defproven Bun [grams] rec/checks (grams [] :fresh true))
        (rec/defproven Bun [grams] rec/checks (grams [] :food-safety true))
        (rec/defproven Bun [grams] rec/checks (grams [] #{42} true))
        (rec/defproven Bun [grams] rec/checks (grams [] "doc" food-safety true))
        (rec/defproven Bun [grams] rec/checks (grams [] food-safety organic true))
        (rec/defproven Bun [grams] rec/checks (grams [] (pos? grams) food-safety true))
        (rec/defproven Bun [grams] rec/checks (grams [] food-safety))])
;; => [true true true true true true true true]
```

## A check body

In a body the fields are locals. A field's name hides any var of the same name for the whole
body: [names.md](names.md) shows the case.

- **A read of an absent field throws**, and the throw fails the check with the failure data
  `{:absent key}`, where `key` is the field's key. `(rec/extant? f)` and
  `(rec/when-extant f body...)` ask first. [absence-and-nil.md](absence-and-nil.md) states the
  rules, and where the two may be written.
- **A failed read from a source throws too**, and fails the check with
  `{:fetch-failed source :cause e}`. A **source** is a function that a body reads with
  `rec/fetch` or `rec/fetch-each`. [sources.md](sources.md) states what a source is, and where
  a read may be written.
- **A body may catch either throw.** The check then passes or fails by what the body returns.
- **Anything else that a body throws is not a failed check.** It propagates out of the call
  that ran the check.

```clojure
(rec/defproven Slice [grams ^:optional butter]
  rec/checks
  (grams  [] (pos-int? grams))
  (butter [] (pos-int? butter))
  (reads-it   [] (< butter grams))
  (catches-it [] (try (< butter grams) (catch Exception _ true))))

(try (map->Slice {::grams 30})
     (catch clojure.lang.ExceptionInfo e
       (into {} (for [[id failure] (:failed (ex-data e))] [id (:data failure)]))))
;; => {::reads-it {:absent ::butter}}

(rec/defproven Burnt [grams]
  rec/checks
  (grams [] (throw (IllegalStateException. "the oven is off"))))

(map->Burnt {::grams 30})
;; IllegalStateException: the oven is off
```

Refused in a body:

- a plain symbol that names no field, no local and no var, as a value or in call position;
- `rec/fetch`, `rec/fetch-each`, `rec/extant?` or `rec/when-extant` that is not in call
  position, or that is given the wrong arguments; `rec/extant?` or `rec/when-extant` of
  anything but a field;
- a read of a source where [sources.md](sources.md) says that none may be written: inside a
  function that the body builds, and inside `locking`;
- `set!` of a field;
- a field named inside a method of a `deftype` that the body defines, and a field of such a
  `deftype` that has a field's name;
- a field named where the compiler evaluates it and the body does not, such as metadata on a
  collection;
- the names `&field`, `&fetch`, `&fetch-each` and `&extant?`, which the library keeps for
  itself.

```clojure
(defn in-stock [kinds] (zipmap kinds (repeat true)))

(mapv refused?
      '[(rec/defproven Bun [grams] rec/checks (grams [] (pos-int? gramz)))
        (rec/defproven Bun [grams] rec/checks (grams [] (no-such-function grams)))
        (rec/defproven Bun [grams] rec/checks (grams [] (map rec/extant? [grams])))
        (rec/defproven Bun [grams] rec/checks (grams [] (rec/fetch in-stock)))
        (rec/defproven Bun [grams] rec/checks (grams [] (let [n grams] (rec/extant? n))))
        (rec/defproven Bun [grams] rec/checks (grams [] (every? #(rec/fetch in-stock %) [grams])))
        (rec/defproven Bun [grams] rec/checks (grams [] (locking grams (rec/fetch in-stock grams))))
        (rec/defproven Bun [grams] rec/checks (grams [] (set! grams 1)))
        (rec/defproven Bun [grams] rec/checks
          (grams [] (deftype Scale [] Object (toString [_] (str grams))) true))
        (rec/defproven Bun [grams] rec/checks
          (grams [] (deftype Scale [grams] Object (toString [_] "a scale")) true))
        (rec/defproven Bun [grams] rec/checks (grams [] ^{:weighed grams} [1]))
        (rec/defproven Bun [grams] rec/checks (grams [] (let [&field 1] true)))])
;; => [true true true true true true true true true true true true]
```

`rec/extant?` or `rec/when-extant` of a required field is not refused. The definition prints a
warning, since a required field is present wherever the check runs.

## The binding of a bundle

A **bundle** is a group of checks over named **inputs**, defined with `rec/defchecks`. A type
**binds** a bundle with a checks section: the bundle's var, then one input clause for each
input of the bundle.

```text
(input [] body ...)
```

- **An input clause** names an input, has an empty wait vector, and takes no flag, no
  docstring and no metadata. Its body is written over the type's fields, as a check body is,
  and reads no source.
- **An input clause runs when a check that reads its input runs**, once for each such check.
- **An input is absent where its clause reads an absent field.** A read of an absent input
  fails the bundle's check with `{:absent :input}`, where `:input` is the input's name as a
  keyword.
- **`^{:when-extant field}` on the bundle's var** skips the binding's checks, as passing, while
  that optional field is absent. A write that adds the field runs them. It is the only metadata
  that a section's head takes.
- **A type binds a bundle once.** `rec/defcopy` makes a copy of a bundle under new names, which
  the type binds as another bundle.

```clojure
(def input-runs (atom 0))

(rec/defproven Tart [grams ^:optional price]
  ^{:when-extant price}
  priced
  (price [] (do (swap! input-runs inc) price))

  rec/checks
  (grams [] (pos-int? grams))
  (price [] (number? price)))

(def tart (map->Tart {::grams 90}))

@input-runs
;; => 0
(assoc tart ::price -2)
;; ExceptionInfo: bakery.loaf/Tart failed 1 check
;;   :bakery.loaf/price-positive (the price is above zero): false, which blocked :bakery.loaf/price-in-cents
(::price (assoc tart ::price 250))
;; => 250
@input-runs
;; => 3
```

The input clause ran once for the failed write, in which `price-positive` alone ran, and twice
for the write that passed, in which both checks of the bundle ran.

**A clause of `rec/checks` replaces one check of a bound bundle** where it is named by that
check's var, with its namespace, and carries the flag `:override`:

```text
(bundle-ns/check [wait ...] :override "docstring"? body ...)
```

The body is written over the type's fields. The check keeps its id, its concerns and its
binding's `:when-extant`, and the bundle's other checks still wait on it. A replacement that
carries a further concern writes both flags in one set: `#{:override organic}`.

```clojure
(rec/defproven Gift [grams]
  priced
  (price [] grams)

  rec/checks
  (grams [] (pos-int? grams))
  (bakery.loaf/price-positive [] :override "a gift is free" true))

(rec/sealed? (map->Gift {::grams 500}))
;; => true
```

Refused in a binding, and in a replacement:

- a bundle that the type binds twice;
- an input clause that names no input of the bundle, an input that no clause binds, and two
  clauses for one input;
- an input clause with a wait, with a flag or with metadata, and one whose body reads a source;
- metadata on the bundle's var other than `:when-extant`, and a `:when-extant` that does not
  name an optional field of the type;
- a clause whose name has a namespace and that lacks `:override`;
- `:override` on a clause that is named by a bare name, by a bundle, or by a check of a bundle
  that the type does not bind;
- an own check whose id is the id of a check of a bound bundle, as where the bundle is defined
  in the type's namespace and both have a check of one name. The clause that means to replace
  that check is written with `:override`.

```clojure
(mapv refused?
      '[(rec/defproven Bun [grams] priced (price [] grams) priced (price [] grams))
        (rec/defproven Bun [grams] priced (cost [] grams))
        (rec/defproven Bun [grams] priced)
        (rec/defproven Bun [grams] priced (price [] grams) (price [] grams))
        (rec/defproven Bun [grams] priced (price [grams] grams))
        (rec/defproven Bun [grams] priced (price [] food-safety grams))
        (rec/defproven Bun [grams] priced (^:fresh price [] grams))
        (rec/defproven Bun [grams] priced (price [] (rec/fetch in-stock grams)))
        (rec/defproven Bun [grams] ^:fresh priced (price [] grams))
        (rec/defproven Bun [grams] ^{:when-extant grams} priced (price [] grams))
        (rec/defproven Bun [grams] ^{:when-extant cost} priced (price [] grams))
        (rec/defproven Bun [grams] ^:fresh rec/checks (grams [] true))])
;; => [true true true true true true true true true true true true]

(mapv refused?
      '[(rec/defproven Bun [grams] priced (price [] grams)
          rec/checks (bakery.loaf/price-positive [] true))
        (rec/defproven Bun [grams] rec/checks (grams [] :override true))
        (rec/defproven Bun [grams] priced (price [] grams)
          rec/checks (bakery.loaf/priced [] :override true))
        (rec/defproven Bun [grams] rec/checks (bakery.loaf/price-positive [] :override true))
        (rec/defproven Bun [grams] priced (price [] grams)
          rec/checks (price-positive [] true))])
;; => [true true true true true]
```

[The guide to bundles](../guides/bundles.md) works through a bundle, a copy and a replacement.
The docstrings of `rec/defchecks` and `rec/defcopy` state the forms that define a bundle and a
copy.

## Method sections

After the checks sections come the type's protocols and interfaces, mixed, written as in
`defrecord`: a protocol or an interface, then its methods.

```text
(name [this parameter ...] body ...)
```

- **The first parameter is the value.** The parameters are plain symbols, and `&` is not among
  them.
- **In a method body the fields are locals**, and the local of an absent field is `nil`. A
  check body differs: there, a read of an absent field throws.
- **`T` in a method body is the value's class**, `(class this)`. It takes no type hint.
- **The constructors are not defined while the methods compile.** A first definition of `T`
  whose method body names `map->T` or `->T` does not compile. A method makes another value by
  writing to `this`, and the write runs the checks.
- **Of the methods of `Object`, a type gives only `toString`.**
- **Type hints on the parameters choose among an interface's methods of one name and one number
  of parameters.**
- **A sealed value is an instance of each interface, and of each protocol's interface**, so a
  direct call of a method dispatches on the class. A **draft**, which is an unchecked map of a
  type made with `rec/draft`, is an instance of none of them.
- **A section need not give every method.** A call of a method that the section's protocol or
  interface declares and the section does not give throws `UnsupportedOperationException`. One
  case differs: where a value already has that method as a map, the call gives the map's
  answer, or throws `AbstractMethodError` where the two methods' return types differ.

```clojure
(label rye)
;; UnsupportedOperationException: no function implements label

(definterface Stamp
  (^String stamp [^String text])
  (^String stamp [^Long number]))

(rec/defproven Box [grams]
  rec/checks
  (grams [] (pos-int? grams))

  Stamp
  (stamp [_ ^String text] (str "text " text))
  (stamp [_ ^Long number] (str "number " number)))

(def box (map->Box {::grams 250}))

[(.stamp ^bakery.loaf.Stamp box "rye") (.stamp ^bakery.loaf.Stamp box (Long. 7))]
;; => ["text rye" "number 7"]
[(instance? bakery.loaf.Stamp box) (instance? bakery.loaf.Stamp (rec/draft box))]
;; => [true false]

(defprotocol Sized
  (size [x]))

(rec/defproven Bin [grams]
  rec/checks
  (grams [] (pos-int? grams))

  Sized)

(try (size (map->Bin {::grams 250}))
     (catch AbstractMethodError e (.getSimpleName (class e))))
;; => "AbstractMethodError"
```

Refused in a method section:

- a checks section after a method section;
- a head that is a class and not an interface, and a protocol or an interface that heads two
  sections;
- metadata on the head;
- a method that is not a list of a name, a vector of parameters and a body; a method with no
  parameter; a parameter that is not a plain symbol;
- a method that the section's protocol or interface does not declare, and a method that it
  declares with another number of parameters;
- a method that more than one method of the interface matches, and a method whose hints match
  none;
- a method written twice with the same number of parameters;
- `equals` and `hashCode`, and every other method of `Object` but `toString`;
- a method that a value already has as a map, such as `count` or `size` with no argument;
- a type hint that names `T`;
- the interfaces `java.util.function.Predicate` and `java.util.function.BiConsumer`;
- interfaces that clash with each other or with a map's: two that give default bodies of one
  method that the section does not give, two whose methods differ only in return type, and one
  whose `print-method` entry Clojure prefers to a map's.

```clojure
(definterface Weighed (^long weight []))
(definterface Tallied (^String weight []))

(mapv refused?
      '[(rec/defproven Bun [grams] Describe (describe [_] "a bun") rec/checks (grams [] true))
        (rec/defproven Bun [grams] java.util.ArrayList (size [_] 1))
        (rec/defproven Bun [grams] Describe (describe [_] "a bun") Describe (label [_] "bun"))
        (rec/defproven Bun [grams] ^:fresh Describe (describe [_] "a bun"))
        (rec/defproven Bun [grams] Describe (describe [] "a bun"))
        (rec/defproven Bun [grams] Describe (describe [_ & more] "a bun"))
        (rec/defproven Bun [grams] Describe (price [_] 1))
        (rec/defproven Bun [grams] Describe (describe [_ extra] "a bun"))
        (rec/defproven Bun [grams] Stamp (stamp [_ x] "a bun"))
        (rec/defproven Bun [grams] Stamp (stamp [_ ^Double x] "a bun"))
        (rec/defproven Bun [grams] Describe (describe [_] "a bun") (describe [_] "a roll"))
        (rec/defproven Bun [grams] Object (equals [_ other] true))
        (rec/defproven Bun [grams] Object (hashCode [_] 1))
        (rec/defproven Bun [grams] Object (finalize [_] nil))
        (rec/defproven Bun [grams] clojure.lang.Counted (count [_] 1))
        (rec/defproven Bun [grams] Sized (size [_] 1))
        (rec/defproven Bun [grams] Describe (describe [^Bun this] "a bun"))
        (rec/defproven Bun [grams] java.util.function.Predicate (test [_ x] true))
        (rec/defproven Bun [grams] java.util.function.BiConsumer (accept [_ x y] nil))
        (rec/defproven Bun [grams] bakery.loaf.Weighed (weight [_] 1) bakery.loaf.Tallied)])
;; => [true true true true true true true true true true
;;     true true true true true true true true true true]
```

[The guide to methods](../guides/methods.md) works through a type with protocols and
interfaces, gives the remedy for several of these refusals, and shows how a protocol is
extended to a type from outside its definition.

## What a constructor and a write throw

A value reads, compares and hashes as a map of its entries, and it is not a record.
[names.md](names.md) compares the two, and
[printing-and-reading.md](printing-and-reading.md) states how a value prints and reads back.

A **write** (`assoc`, `dissoc`, `conj`, `merge`, `into`) runs the checks that read a key that
the write changes, and returns a new value or throws. [writes.md](writes.md) states which
writes of several keys are one write.

A constructor or a write that fails throws an `ex-info`:

| `:error` | Thrown where |
|---|---|
| `:recognitum/undeclared-keys` | The entries hold a key that the type does not declare. Thrown before any check runs. |
| `:recognitum/check-failed` | A check fails, or a required field is absent. |

```clojure
(defn error-of
  "The `:error` of the ex-info that calling `f` throws."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:error (ex-data e)))))

[(error-of #(map->Loaf {::kind "rye" ::grams 800 ::crust :dark}))
 (error-of #(map->Loaf {::kind "rye"}))
 (error-of #(assoc rye ::grams 300))]
;; => [:recognitum/undeclared-keys :recognitum/check-failed :recognitum/check-failed]
```

[failures.md](failures.md) states the rest of the data. Two more calls throw, and neither
throws an `ex-info`: `empty` of a value throws `UnsupportedOperationException`, and the class's
own constructor, `(T. ...)`, throws `SecurityException`.

## A definition that fails

A definition is one form. It defines at the top level and inside another form alike.

A definition fails where a section is refused, or where a check or a method does not compile.
A definition that fails leaves nothing: no class, no constructor and no var. Where the name
already named a type, the earlier definition stays current.

- **A refusal** is an `ex-info` whose `:error` is `:recognitum/refused`. Its message names the
  type and, where it can, the clause and its line, and says what to change. Where the form is
  refused as it expands, the `ex-info` is the cause of the compiler's exception.
- **Where the compiler itself rejects a body**, as for a method that calls an unknown function,
  the compiler's exception has no such cause.

```clojure
(rec/defproven Bun [grams]
  rec/checks
  (grams [fresh] (pos-int? grams)))
;; ExceptionInfo: bakery.loaf/Bun, line 3: wait fresh of grams is not a check of Bun. Its own checks: grams

(defn fails-without-a-refusal?
  "Whether evaluating `form` throws, and no refusal is among the causes."
  [form]
  (try (eval form) false
       (catch Throwable _ (not (refused? form)))))

(fails-without-a-refusal?
 '(rec/defproven Bun [grams]
    rec/checks
    (grams [] (pos-int? grams))

    Describe
    (describe [_] (no-such-function grams))))
;; => true

[(resolve 'Bun) (resolve 'map->Bun) (resolve '->Bun)]
;; => [nil nil nil]

(let [inside :another-form]
  (rec/defproven Bun [grams]
    rec/checks
    (grams [] (pos-int? grams))))

(rec/sealed? (->Bun 60))
;; => true

(refused? '(rec/defproven Bun [grams] rec/checks (grams [fresh] (pos-int? grams))))
;; => true
(rec/sealed? (->Bun 60))
;; => true
```

## Redefinition

Evaluating the form again redefines `T`: the new definition is the type's **current
definition**, and the earlier one is a **displaced definition**. A value of a displaced
definition keeps its entries and is not sealed. A write that changes it, a method that the
definition lists other than `toString`, and each call that would seal it or run checks on it
throw an `ex-info` whose `:error` is `:recognitum/displaced`. A constructor held from before
the redefinition throws one whose `:error` is `:recognitum/displaced-constructor`.
`(rec/seal (rec/draft v))` proves such a value under the current definition.

[redefinition.md](redefinition.md) states every rule, with what counts as a redefinition, and
what a draft, a class and a protocol extension held from before it do.

## Every refusal

Every row is a refusal of the definition form, with the `:error` `:recognitum/refused`. The
section named in each row lists the cases.

| Refused | Section |
|---|---|
| A name that is not a plain symbol, or that already names a var or another class in the namespace. | [What a definition makes](#what-a-definition-makes) |
| Fields that are not a vector of one or more plain symbols, a field written twice, and more than 250 fields. | [Fields](#fields) |
| A clause before any head, a head that names no bundle, protocol or interface, and `rec/checks` twice. | [Sections](#sections) |
| A clause that lacks its name, its wait vector or its body, two clauses of one name, and metadata on a clause, its name or its waits. | [A check clause](#a-check-clause) |
| A wait that names no check the type has, and waits that form a cycle. | [Waits](#waits) |
| A flag that is no concern and not `:override`, a flag out of its place, and a check whose whole body is a concern. | [Flags](#flags) |
| A body that names what it cannot read, or that reads a source where no read may be written. | [A check body](#a-check-body) |
| A binding that does not give each input one clause, a bundle bound twice, a wrong `:when-extant`, and a replacement without `:override` or of a check that the type does not have. | [The binding of a bundle](#the-binding-of-a-bundle) |
| A checks section after a method section, a method that the section cannot give, and interfaces that clash. | [Method sections](#method-sections) |

Two failures of a definition are not refusals:

- A body that the compiler rejects throws the compiler's exception, with no refusal as its
  cause.
- `rec/fetch`, `rec/fetch-each`, `rec/extant?` or `rec/when-extant` written outside a check
  body throws `IllegalStateException` when the form expands, as the cause of the compiler's
  exception.

A mistake that only a linter can see, such as a misspelled name in another form, is not
refused, and the definition does not fail. [editor-support.md](editor-support.md) states what
the clj-kondo configuration reports.

## A `rec/defproven-in` type

`rec/defproven-in` takes the form that this page states, refuses what `rec/defproven` refuses,
and makes the same names. The type differs in what runs its checks: nothing does but a call
that asks to.

| | A `rec/defproven` type | A `rec/defproven-in` type |
|---|---|---|
| `map->T`, `->T`, the tagged literal | Run every check. | Check nothing. |
| A write | Runs the checks that read a key it changes. | Checks nothing. |
| A key that the type does not declare | Throws `:recognitum/undeclared-keys`. | The same. |
| A required field | Present in every value. | May be absent. |
| Proof | `rec/sealed?` | `rec/proves?`; `rec/sealed?` is always false. |
| The type's protocols and interfaces | Every sealed value implements them. | Every value implements them, whatever it has passed. |
| Drafts | `rec/draft` makes one. | None: `rec/draft`, `rec/clean` and `rec/drafting` throw `:recognitum/no-drafts`. |

```clojure
(rec/defproven-in Dough [grams ^:optional proofed]
  rec/checks
  (grams   [] (pos-int? grams))
  (proofed [] (boolean? proofed)))

(def dough (map->Dough {}))

[(rec/sealed? dough) (rec/proves? dough rec/every)]
;; => [false false]
[(error-of #(assoc dough ::flour :rye)) (error-of #(rec/draft Dough))]
;; => [:recognitum/undeclared-keys :recognitum/no-drafts]

(def weighed (assoc dough ::grams 500))

(rec/check weighed rec/every)
;; => true
(rec/proves? weighed rec/every)
;; => true
(rec/proves? (assoc weighed ::grams 600) rec/every)
;; => false

(refused? '(rec/defproven-in Batter [grams] rec/checks (grams [fresh] true)))
;; => true
```

A value carries, in place, the checks that passed on its entries, and every holder of the
value sees what a run writes there. [memory.md](memory.md) states what a value remembers and
what makes it forget, [selections.md](selections.md) states what `rec/proves?` answers, and
[redefinition.md](redefinition.md) states what a value of a displaced definition does.
[The guide to values checked in parts](../guides/checked-in-parts.md) works through such a
type.

## Not promised

- The wording of a refusal's message, and which refusal is thrown where a form has more than
  one fault.
- Whether a form is refused as it expands or when it is evaluated.
- What a method body that names `map->T` or `->T` does where the form is evaluated again while
  an earlier definition's constructors are still defined.
