# recognitum

Types whose values carry proof that their checks passed.

`rec/defproven` defines a type from its fields and its named **checks**. Every way to make a
value of the type runs the checks or throws, so holding a value is holding proof that they
passed: `(rec/sealed? x)` is the whole test, and `(instance? Heist x)` gives the same answer
until `Heist` is redefined. A value reads and compares as a map, and every write to it is
checked.

```clojure
(require '[recognitum.core :as rec])
```

## Install

Add the library to `deps.edn` as a git dependency:

```clojure
{:deps {io.github.galdre/recognitum {:git/tag "v0.2.0"}}}
```

A git dependency also needs the sha of its commit. Run `clj -X:deps git-resolve-tags` once:
it finds the commit of each `:git/tag` in `deps.edn` and adds its `:git/sha`.

Report problems as issues at <https://github.com/galdre/recognitum/issues>.

## A heist

```clojure
(ns crew.heist
  (:require [recognitum.core :as rec] [crew.house :as house]))

(rec/defproven Heist [name crew take cuts ^:optional getaway]
  rec/checks
  (name    [] "the job has a name" (non-blank? name))
  (crew    [] "the crew is a set of names" (crew-set? crew))
  (take    [] "the take is a whole number" (non-neg-int? take))
  (cuts    [] "each cut is a whole number" (cuts-map? cuts))
  (getaway [] "the getaway driver is named" (non-blank? getaway))

  (cuts-sum-to-take []
    "the cuts add up to the take"
    (sums-to take cuts))
  (only-crew-get-cuts [cuts-sum-to-take]
    "only the crew gets a cut"
    (every? crew (keys cuts)))
  (crew-vetted []
    "the house has vetted everyone on the crew"
    (every? true? (vals (rec/fetch-each house/vetted crew))))
  (getaway-not-crew []
    "the driver stays out of the vault"
    (rec/when-extant getaway (not (contains? crew getaway)))))
```

This defines the class `crew.heist.Heist`, imported into the namespace, and two constructors:

```clojure
(map->Heist {::name "The Italian Job" ::crew #{"Charlie" "Stella"} ::take 2000
             ::cuts {"Charlie" 1000 "Stella" 1000}})
(->Heist "The Italian Job" #{"Charlie"} 1000 {"Charlie" 1000} "Handsome Rob")
```

Each field's key is a keyword in the defining namespace, named after the field: `::name` here.
A field marked `^:optional` may be absent; every other field must be present. `->Heist` takes
every field, and `nil` counts as present.

Optional means absent, never `nil`. An optional field that holds `nil` is present, and its
shape check runs on `nil`: `(non-blank? getaway)` fails. A caller that means "no getaway", or
"no change" in an update, leaves the key out.

This example is `dev/demo/heist.clj`, in the namespace `demo.heist`, which also defines the
plain predicates the checks call (`non-blank?`, `crew-set?` and the rest). `dev/demo/house.clj`
is a fake `house` source. `clojure -M:dev -m demo.heist-run` runs the example end to end and
prints each step.

## Checks

A clause after `rec/checks` is `(name [waits] flags? "doc"? body...)`. The flags are a
concern or `:override`, described under Bundles.

- A check passes when its body returns exactly `true`. Anything else it returns is its
  failure data.
- Its id is a keyword in the defining namespace: `::cuts-sum-to-take`.
- A check named after a field is that field's **shape check**. The shape check of an optional
  field passes where the field is absent.
- A check waits on the shape check of each field its body reads, `extant?` included. The wait
  vector names any other checks that must pass first; naming a shape check there changes
  nothing. If a check it waits on fails, this check does not run and is reported as blocked.
  Above, `cuts-sum-to-take` reads `take` and `cuts`, so it waits on their shape checks and
  never adds up a take that is not a number.

### What a body sees

Inside a body the fields are locals. A macro used in a body sees them in `&env` as compiler
locals, with their type hints. As with any local, a `deftype` that a body defines does not
see them in its methods: a field named there is refused when the type is defined. Pass the
field to the deftype as one of its own fields, or use `reify`, whose methods close over it.

- A read of an absent field throws, which fails the check with `{:absent key}`, the field's key.
  `(rec/extant? f)` asks whether `f` is present, and `(rec/when-extant f body...)` is
  `(if (rec/extant? f) (do body...) true)`.
- `(rec/fetch source k)` reads one key from a **source**, and `(rec/fetch-each source ks)`
  reads several in one call and returns a map from key to answer. A source is a function from a
  vector of distinct keys to a map from key to answer; a key it leaves out reads as `nil`. A
  read from a source that throws fails the check with `{:fetch-failed source :cause e}`, where
  `e` is what the source threw.
- A body may read a dynamic var; it sees the binding in force where the check runs. A draft
  remembers a pass as it remembers any other, so a check that passed under one binding is not
  run again under another until a write or `rec/recheck` asks for it.
- A body that runs, runs once, from start to end, in each run of the checks; a check assumed
  as passing or blocked does not run. An effect in a body therefore happens at most once per
  run.
- A body never throws on purpose. The absent read and the failed read are ordinary exceptions
  that a body may catch; uncaught, they fail the check. Anything else a body throws is a bug in
  the check, not a claim about the data. It propagates out of the constructor, write, `seal`,
  `check`, `recheck` or `check-all` that ran the check, and that call returns nothing for any
  value.

A body reads a source and calls functions through their vars, so a test stubs either with
`with-redefs`:

```clojure
(with-redefs [house/vetted (fn [ks] (zipmap ks (repeat true)))]
  (map->Heist job-entries))
```

The four body macros work only inside a check body, in call position, and outside any function
the body builds (`fn`, `#(...)`, `for`, `lazy-seq`, `delay`). Anywhere else they fail to
compile. This keeps a read where the engine can see it: a check engine may batch the reads of
many checks and values into fewer calls.

## Building values

`map->Heist`, `->Heist` and the tagged literal run every check, or throw:

```clojure
(map->Heist {::name "Job" ::crew #{"Charlie"} ::take 10 ::cuts {"Charlie" 9}})
;; ExceptionInfo: crew.heist/Heist failed 1 check
;;   :crew.heist/cuts-sum-to-take (the cuts add up to the take): false, which blocked :crew.heist/only-crew-get-cuts
```

A value prints as a tagged literal, `#crew.heist/Heist {...}`. For `read` to accept it, add a
line to the project's `data_readers.cljc`:

```clojure
{crew.heist/Heist crew.heist/map->Heist}
```

For `clojure.edn`, pass `(rec/data-readers)` as `:readers`.

The class's own JVM constructor is not a way in: `(Heist. ...)` throws
`SecurityException "no key"`, since it takes a key that only the library holds. Call
`map->Heist` or `->Heist`.

`(rec/sealed? x)` asks whether `x` is a value of the current definition of its type, and
`(rec/draft? x)` whether it is a draft.

Evaluating `defproven` again defines a new class. Values of the old class keep their entries
and still read and print as before, but they are no longer sealed: `rec/sealed?` answers false,
and every write that changes one and every method of the type's own protocols and interfaces
throws, `toString` excepted:

```clojure
(assoc old-heist ::take 12)
;; ExceptionInfo: crew.heist/Heist was redefined: this value is of an earlier definition, so it
;; is not sealed and refuses writes and its type's methods. To prove it under the current
;; definition: (rec/seal (rec/draft v))
```

`rec/draft` of an old value gives a draft of the new definition holding its entries, and
`rec/seal` of that draft runs the new checks and returns a value of the new class. Reading an
old value's printed form does the same, since the tag reads with the new `map->Heist`. Where
the name no longer names a definition of the type (the namespace unmapped it, or it now names
a plain record), `rec/draft` of an old value throws, saying the type has no current
definition. A draft opened before the redefinition still reads its entries, but proves
nothing, whatever it remembered, and its seal throws. A write
that changes nothing may return the old value unchanged, still not sealed: `assoc` of the
identical value or `dissoc` of an absent key does, while `into` and `assoc` of an equal value
that is not identical throw.

A constructor held from before the redefinition, as `(def make map->Heist)` holds it, makes
nothing: it throws, naming the current constructor.

```clojure
(make {::name "Ocean" ...})
;; ExceptionInfo: crew.heist/Heist was redefined: this constructor is of an earlier definition
;; and makes nothing. Call the current crew.heist/map->Heist
```

Code that ran `(instance? Heist x)` before the redefinition still names the old class, so there
it is true of an old value, which is not sealed. Code that first runs after the redefinition
names the new class, even code compiled before it. `rec/sealed?` answers false for an old value
wherever it is asked, so a sink that may outlive a redefinition at the REPL asks `rec/sealed?`.

A definition that fails leaves nothing: where a check or a method does not compile, or a
protocol or an interface is refused, the name reaches no class and no constructor, and an
earlier definition under the name stays current, its values sealed and its methods answering.
The checks and the methods compile as one form, before anything is defined, so a definition
works the same at the top level and inside a `let` or a `when`, and under a tool that wraps
or expands each top-level form, as `clojure.walk/macroexpand-all` or a coverage tool such as
cloverage does.

## Writing values

`assoc`, `dissoc`, `conj`, `merge` and `into` on a value run the checks that read a key the
write changes, and return a new value or throw. A write of several keys at once is one write,
checked on the result, so its order never matters:

```clojure
(merge job {::take 3000 ::cuts {"Charlie" 1500 "Stella" 1500}})   ; one write, checked once
(assoc job ::getaway "Charlie")
;; ExceptionInfo: crew.heist/Heist failed 1 check
;;   :crew.heist/getaway-not-crew (the driver stays out of the vault): false
```

Every type is closed: a value refuses a key its type does not declare. `empty` throws, since no
type with a required field has an empty value.

## Drafts

A **draft** is an unchecked map of a type, for a value built in steps. It accepts any write,
including keys the type does not declare, and remembers which checks pass on its entries.
`rec/seal` checks it and returns the value:

```clojure
(defn plan-from-form [partial-plan]
  (-> (rec/draft Heist) (into partial-plan) (rec/seal)))
```

- `(rec/draft Heist)` holds nothing and passes nothing. `(rec/draft job)` holds the value's
  entries and passes every check. A draft of a draft is that draft.
- A write returns a new draft that forgets the checks reading a key it wrote.
- `rec/seal` runs only the checks the draft does not remember as passing. A failed seal
  still remembers what passed, so after the draft is mended the next seal runs only the rest.
  A draft that holds an undeclared key does not seal; `rec/clean` drops such keys.
- `(rec/check d sel)` runs the selected checks, and what they wait on, that `d` does not
  remember, and remembers the result. `(rec/recheck d sel)` runs the selected checks even if
  `d` remembers them; use it when a source's answer may have changed.

The memory cannot be forged: marks are tied to the entries they were set for and can be set
only by the type's own checked code.

`rec/seal-all` seals every draft in a shape of plain data at once, and returns the shape with
each draft replaced by its value:

```clojure
(rec/seal-all {:jobs [draft-1 draft-2] :backup draft-3})
;; {:jobs [#crew.heist/Heist {...} #crew.heist/Heist {...}] :backup #crew.heist/Heist {...}}
```

- It walks maps (keys too), vectors, lists and sets. A list stays a list; any other sequence,
  a lazy one included, becomes a vector. A sealed value is not entered and comes back as it is.
- It enters the fields of a draft, and seals the drafts it finds there first: a draft holding
  drafts is checked holding their values. The drafts at one level, counted from the innermost,
  are checked in one pass, as `rec/check-all` checks them, so they share each source's calls.
- It is all or nothing. Where any draft fails, it throws one `ex-info` with `:error`
  `:recognitum/drafts-failed`. Every draft is still checked, so the throw names every failure.
  `:failures` maps the path of each draft that failed to what `rec/seal` would have thrown for
  it; `:drafts` is the shape with every draft in place, each remembering what passed. Mend the
  drafts at those paths and seal again; the second call runs only what is left:

```clojure
(try (rec/seal-all plans)
     (catch clojure.lang.ExceptionInfo e
       (let [{:keys [failures drafts]} (ex-data e)]
         (rec/seal-all (reduce-kv (fn [ds path _] (assoc-in ds (conj path ::take) 3000))
                                  drafts failures)))))
```

A path is what `get-in` takes at each step, with an index for a list or a sequence. In
`:drafts` a sequence is already a vector, so `assoc-in` follows its path; a list stays a list,
which `assoc-in` cannot enter. A draft used as a map key has a path ending in
`:recognitum.core/key`.

`(rec/drafting-all shape f)` opens every sealed value in `shape` as a draft, calls `f` on the
result, and seals what `f` returns with `rec/seal-all`. `(rec/drafting v f)` does the same for
one value: given a sealed value, it opens it, calls `f` and seals the result; given a draft, it
calls `f` and returns the result unsealed. So a step written with `rec/drafting` seals a value
on its own, and inside `rec/drafting-all` leaves the seal to it:

```clojure
(defn rename [heist n] (rec/drafting heist #(assoc % ::name n)))

(rename italian-job "The Bank Job")                                ; a sealed Heist
(rec/drafting-all [job-1 job-2] #(mapv (fn [j] (rename j "Again")) %))   ; sealed once, together
```

## Bundles

A **bundle** is a group of checks over named inputs, defined once and bound into many types.

```clojure
(ns app.perms
  (:require [recognitum.core :as rec] [app.db :as db]))

(rec/defconcern permission "Checks on the acting user's rights.")

(rec/defchecks collection-write
  "The checks of a write to a collection."
  [user collection-id]
  rec/checks
  (collection-exists []
    "the collection is on file"
    (some? (rec/fetch db/collections collection-id)))

  (may-write [collection-exists] ::permission
    "the acting user may write to the collection"
    (db/can-write? user (rec/fetch db/collections collection-id))))

(rec/defcopy current-collection-write collection-write
  {collection-exists current-collection-exists
   may-write         current-may-write})
```

- `defchecks` defines the bundle var and one var per check: `perms/may-write`. A docstring
  after the bundle's name is the bundle var's, and one after a check's waits is the check's.
- `defconcern` defines a concern. A clause carries it when `::permission` follows the clause's
  waits; several concerns are written as a set, `#{::permission ::audit}`. A keyword or set
  alone after the waits is the body. A concern that no `defconcern` defines is refused, and so
  is metadata on a clause, its name or its waits, which the macros do not read.
- `defcopy` copies a bundle under new names. Its map names every check of the bundle exactly
  once. The copy's ids are in the copying namespace, and its checks keep their concerns and
  docstrings. It takes a docstring after its name, as `defchecks` does.

A type binds a bundle with the bundle's var followed by one `(input [] expression)` clause per
input, each an expression of the type's fields:

```clojure
(rec/defproven Card [id name collection-id archived
                     ^:optional acting-user ^:optional stored-collection-id]
  perms/collection-write
  (user          [] acting-user)
  (collection-id [] collection-id)

  ^{:when-extant stored-collection-id}
  perms/current-collection-write
  (user          [] acting-user)
  (collection-id [] stored-collection-id)

  rec/checks
  (name [] (non-blank? name))
  (moves-only-where-allowed [perms/may-write perms/current-may-write] ::perms/permission true))
```

- An input clause runs only when a check that reads its input runs, once for each such
  check. A check its waits block runs none.
- An input whose clause reads an absent field is absent: here, a card with no acting user
  fails `may-write` with `{:absent :user}`, the input's key. A throw from a clause propagates
  as a throw from a body does.
- A bundle check reads the fields that the clauses of its inputs read, so it waits on their
  shape checks.
- `^{:when-extant f}` on a binding skips its checks, as passing, while the optional field `f`
  is absent. A later write of `f` runs them.
- In a bundle's body, `rec/extant?` and `rec/when-extant` take an input as a type's body takes
  a field. In an input clause they take a field, with the same meaning: so
  `(user [] (rec/when-extant acting-user acting-user))` gives `true` where the field is absent.
  To pass an absent field on as an absent input, read it: `(user [] acting-user)`.
- A wait names an own check by its bare name, a bundle check by its qualified var, or every
  check of a bundle by the bundle's qualified var: `perms/may-write`, or `app.card/positives`
  for a bundle `positives` defined in the type's own namespace. A bare `positives` is read as
  an own check, and refused.
- `(perms/may-write [waits] :override body)` in `rec/checks` replaces that check of a bound
  bundle with a body over the type's fields. It keeps the check's id and concerns, and its
  binding's `:when-extant`. With concerns of its own, it is written in one set:
  `#{:override ::audit}`.

## Protocols

The full form is:

```clojure
(rec/defproven T [fields...]
  rec/checks clauses...          ; the checks sections, in any order:
  bundle input-clauses...        ;   rec/checks and the bundle bindings
  Protocol (method [this args...] body...)...
  Interface (method [this args...] body...)...
  Object (toString [this] body...)
  ...)
```

After the checks sections come the type's own protocols and interfaces, mixed, written as in
`defrecord`: a protocol or an interface, then its methods. In a method body the fields are
locals, nil where an optional field is absent, and the first parameter is the value. `recur`
goes to the method's head without the value.

```clojure
(defprotocol Describe (describe [x]))

(rec/defproven Heist [name crew take cuts ^:optional getaway]
  rec/checks
  (name [] (non-blank? name))
  ...
  Describe
  (describe [_] (str name ", " (count crew) " crew" (when getaway (str ", driven by " getaway)))))
```

- Values of the type are instances of each interface and of each protocol's interface,
  written values included, so a protocol call and a direct call of the interface's method
  (`(.describe v)`) dispatch on the class. Drafts are not; the drafts of every type share one
  class, `recognitum.record.Draft`.
- Where an interface has two methods of one arity, type hints on the parameters choose one:
  `(tag [this ^String s] ...)`. A method that more than one method matches is refused, and so
  is a method the interface does not declare.
- Of `Object`, a type gives only `toString`. `str` of a value is its `toString` where the type
  gives one, else its printed form; printing always shows the tagged map. `equals` and
  `hashCode` are refused: a value's equality and hash are its map's.
- A protocol method that a map already has, such as `size` or `count` with no argument or
  `valAt` with one, is refused when `defproven` expands, as `defrecord` refuses it. The message
  names the two remedies: rename the method, or extend the protocol to the type with
  `extend-protocol` after the definition. A method extended that way is not guarded (below).
  A protocol that the type lists with such a method at another arity defines, and a call of
  the method at the map's arity throws `AbstractMethodError`. An interface's method that a map
  already has, such as `count` of `clojure.lang.Counted`, is refused too: leave it out, and the
  map's method answers.
- Interfaces that cannot be implemented together are refused when `defproven` expands: two
  that give default bodies of one method the type does not give, an interface that the
  proof's drafts implement (`java.util.function.Predicate` and `BiConsumer`), or one whose
  `print-method` entry is preferred to the map's. Every refusal of the proof is made then, at
  compile time; the proof asks again when the type is defined, and a refusal there, where an
  interface or a print entry changed in between, leaves nothing.
- A checks section after a protocol or an interface is refused: the checks come first.
- In a method body `Heist` is the value's class, `(class this)`, as a value: `(instance? Heist
  x)` works. It takes no type hint, since the class does not exist while the methods compile.
  A method body may not call `map->Heist` or `->Heist`, as with `defrecord`.
- A protocol may also be extended to the type from outside, with `extend-protocol` or
  `extend-type`, as to any class. Such methods are not the type's own: values of an earlier
  definition still answer them.
- From another namespace, a type hint or an `extend-protocol` names the class by its full
  name, `crew.heist.Heist`, or by the name `(:import [crew.heist Heist])` gives it. An alias
  does not work: `heist/Heist` names a var, not the class.

## Selecting and asking

A **selection** names some of a type's checks:

| Selection | Selects |
|---|---|
| `::cuts-sum-to-take` | that check |
| `perms/permission`, `::perms/permission` | the checks carrying the concern |
| `perms/collection-write`, `perms/may-write` | a bundle's checks, or one of them |
| `rec/every`, `rec/shape`, `rec/pure` | every check, every shape check, every check that reads no source |
| `(rec/fetching house/vetted)` | the checks that read that source |
| `(rec/reading ::crew)` | the checks that read that field, directly or through an input |
| `(rec/except s ...)`, `(rec/union s ...)` | what `s` selects less the rest; what any selects |

A keyword names a concern or a bundle check through the var `defconcern` or `defchecks` made
for it; any other keyword is a type's own check id. A keyword that names no such var and no
check of a type its namespace defines is refused when `rec/except` or `rec/union` builds the
selection. An own check id that a type lacks is refused when the selection meets that type;
the message gives the type and the id. Otherwise, a selection that names nothing in a type
selects nothing there: a concern no check of the type carries, or a bundle the type does not
bind.

- `(rec/check-all xs sel)` runs what `rec/check` would run on each value of `xs`, which may be
  of several types, in one pass of the engine, so values that read the same source can share
  its calls. Each draft, and each value of a `rec/defproven-in` type, remembers what passed
  and forgets what failed, as under `rec/check`, so a later seal of each runs only the rest. It
  returns one answer per value, in order.
- `(rec/proves? x sel)` is true for every sealed value of a type's current definition. For a
  draft or a value of a `rec/defproven-in` type, it asks what `x` remembers, including the
  shape checks of every field `x` must or does hold.
- `(rec/proven-checks x)`, `(rec/proven-concerns x)` and `(rec/checks-of sel x-or-class)`
  return check ids and concern ids.

A selected check pulls in what it waits on, even a check that `rec/except` removed. The report
then explains, under `:pulled-back`, which check waited on it.

## Failure reports

`rec/check`, `rec/recheck` and each answer of `rec/check-all` are `true` or a report:

```clojure
{:failed  {:crew.heist/take {:data false
                             :doc "the take is a whole number"
                             :blocked #{:crew.heist/cuts-sum-to-take
                                        :crew.heist/only-crew-get-cuts}}}
 :blocked #{:crew.heist/cuts-sum-to-take :crew.heist/only-crew-get-cuts}}
```

Under each failed check, `:blocked` holds the checks its failure kept from running, directly or
through another blocked check. A constructor, a write or a seal that fails throws `ex-info`
whose data is this report with `:error :recognitum/check-failed` and `:type`. The other errors
about a value's entries are `:recognitum/undeclared-keys` and `:recognitum/missing-fields`,
each with the `:keys`.

A missing required field fails each check that reads it with `{:absent key}`, its shape check
included. `:recognitum/missing-fields` comes only when every check passes and no check read the
missing field.

## Values checked in parts

A `rec/defproven` value passes every check wherever it is held. Some values are filled in over
several steps, and different places ask different checks of them. `rec/defproven-in` defines a
type for such values, from the same form as `rec/defproven`, except that nothing runs its checks
but a call that asks to: `map->T`, `->T`, the tagged literal and every write check nothing. A
key the type does not declare is still refused at the write.

A draft is also filled in over steps, but it is sealed against every check, and its value then
passes every check. A value of a `rec/defproven-in` type is checked against whatever
selection its holder asks for, and proves the checks that passed on it.

A value carries, in place, the checks that passed on its entries. `rec/check`, `rec/recheck`,
`rec/check-all`, `rec/seal` and `rec/seal-all` run checks on it and record what passed, and
every holder of the value sees the record. A write returns a new value that keeps the record,
less the checks that read a key the write changes. A value of such a type is never sealed, and
it is an instance of its class whatever it has passed, so code that needs proof asks
`rec/proves?`. The type has no drafts: `rec/draft`, `rec/clean` and `rec/drafting` refuse it.

The second example, `dev/demo/potion.clj`, is a potion that an apothecary brews, bottles and
sells, and that the queen may send for. The concern `shop` marks what the shop asks of a potion,
and `court` what the queen's court asks:

```clojure
(rec/defconcern shop "What the shop needs before it sells a potion.")
(rec/defconcern court "What the court needs before the queen drinks a potion.")

(rec/defproven-in Potion [name recipe ^:optional label ^:optional price ^:optional taster]
  rec/checks
  (name   [] "the potion has a name" (non-blank? name))
  (recipe [] "the recipe maps each herb to its drams" (recipe? recipe))
  (label  [] "the label is written" (non-blank? label))
  (price  [] "the price is a whole number of pennies" (pos-int? price))
  (taster [] "the taster is named" (non-blank? taster))

  (labelled [] ::shop
    "the label names every herb"
    (every? #(str/includes? label %) (keys recipe)))
  (priced [] ::shop
    "the potion has a price"
    (rec/extant? price))
  (licensed [] ::shop
    "the guild licenses every herb"
    (every? true? (vals (rec/fetch-each guild/licensed (keys recipe)))))

  (tasted [] ::court
    "a taster drank it first"
    (rec/extant? taster))
  (fit-for-the-queen [] ::court
    "it holds nothing the queen cannot abide"
    (not-any? the-queen-cannot-abide (keys recipe))))
```

`the-queen-cannot-abide` is the set `#{"garlic" "mandrake root"}`, and `guild/licensed` is a
source that answers, for each herb, whether the apothecaries' guild licenses it.

A brewed potion has passed nothing. `rec/check` runs the checks a selection names, and the
potion records what passed:

```clojure
(def brewed (map->Potion {::name "Draught of Courage"
                          ::recipe {"dragon pepper" 2 "garlic" 1 "honey" 3}}))
(rec/proves? brewed rec/shape)   ;; => false
(rec/check brewed rec/shape)     ;; => true
(rec/proves? brewed rec/shape)   ;; => true

(def bottled (assoc brewed
                    ::label "Draught of Courage: dragon pepper, garlic, honey"
                    ::price 12))
(rec/check bottled shop)         ;; => true
(rec/proves? bottled shop)       ;; => true
(rec/proves? bottled court)      ;; => false
```

A write forgets each check that reads a key it changes. The recipe's shape check, `labelled`
and `licensed` read the recipe, so a new recipe forgets them, and the potion no longer passes
the shop's checks:

```clojure
(def mended (assoc bottled ::recipe {"dragon pepper" 2 "moonwort" 1 "honey" 3}))
(rec/proves? mended shop)        ;; => false
(rec/proven-checks mended)       ;; => #{::name ::label ::price ::taster ::priced}
(rec/proves? bottled shop)       ;; => true
```

The shape check of `taster` passed when `rec/shape` was checked, since an optional field's
shape check passes where the field is absent.

## Contexts

`(rec/defcontext name doc sel)` defines a var that holds the selection `sel`. A context names
the checks that one place asks of a value. It means nothing beyond its selection: every
function that takes a selection takes a context, and answers as it answers for `sel`. The
potion has two:

```clojure
(rec/defcontext on-the-shelf
  "Sold in the shop: every check but the court's."
  (rec/except rec/every court))

(rec/defcontext at-court
  "Served to the queen: every check but the shop's."
  (rec/except rec/every shop))
```

Each place asks for the shape check of every field, and for its own concern's checks but
not the other's.

`(rec/seal v sel)` seals a value of a `rec/defproven-in` type against `sel`. It runs the checks
`sel` selects that `v` has not passed, the checks they wait on, and the shape check of each
field `v` must or does hold. It returns `v` itself, recording what passed, or throws as a
constructor throws. After it returns, `(rec/proves? v sel)` is true. One potion can be fit for
one place and not for the other:

```clojure
(identical? bottled (rec/seal bottled on-the-shelf))   ;; => true
(rec/seal bottled at-court)
;; ExceptionInfo: demo.potion/Potion failed 2 checks
;;   :demo.potion/fit-for-the-queen (it holds nothing the queen cannot abide): false
;;   :demo.potion/tasted (a taster drank it first): false

(def served (assoc mended ::taster "Sir Gulp"))
(identical? served (rec/seal served at-court))         ;; => true
(rec/proves? served on-the-shelf)                      ;; => false
(rec/check served on-the-shelf)
;; => {:failed {::labelled {:data false :blocked #{} :doc "the label names every herb"}}
;;     :blocked #{}}

(def relabelled (assoc served ::label "Draught of Courage: dragon pepper, moonwort, honey"))
(identical? relabelled (rec/seal relabelled on-the-shelf))   ;; => true
(rec/proves? relabelled at-court)                            ;; => true
```

Writing the label forgot only the checks that read the label, so `relabelled` still passes the
court's checks, and its seal on the shelf ran only `label` and `labelled`.

- `(rec/seal v)` seals against `rec/every`.
- A draft seals against every check: `(rec/seal d sel)` throws, running nothing, unless `sel`
  is `rec/every`.
- `(rec/seal-all shape sel)` seals each value of a `rec/defproven-in` type in `shape` in place
  against `sel`, and each draft against every check. Without `sel`, it seals both against
  every check. `rec/drafting-all` leaves such values as they are.
- `rec/check-all` checks a batch against a context in one pass, so the potions share the
  guild's calls: `(rec/check-all potions on-the-shelf)`.

### Sinks and their gates

A **sink** is a function whose effect depends on checks having passed: a sale, a write, a
payment. Three things make a sink safe, and each has one home.

- The **proof** lives in the value. `rec/proves?` says that the checks ran on exactly this
  value; a plain map with the same entries proves nothing. A proof is a fact about the past, so
  a sink asks it of the value it is handed, right before it acts.
- The **gate** lives in the sink. Only the code that receives a value can refuse one without
  proof. With contexts, proof is per context, so each sink names the context it needs.
- **Coverage**, the assurance that every sink has its gate, lives in a test or a lint, since
  neither a value nor a sink can see the rest of the code.

In `demo.potion`, selling gates on the shop's context:

```clojure
(defn- gate
  "Throws unless `potion` is proven against the context held by the var `context`."
  [potion context sink]
  (when-not (rec/proves? potion @context)
    (throw (ex-info (str sink " takes only a potion proven " (:name (meta context)))
                    {:error ::not-proven :sink sink :context (symbol context)}))))

(defonce till (atom []))

(defn ring-up!
  "Records the sale of `potion` in the shop's till, and returns the receipt. Refuses a potion
  not proven `on-the-shelf`."
  [potion]
  (gate potion #'on-the-shelf 'ring-up!)
  (let [receipt {:sold (::name potion) :pennies (::price potion)}]
    (swap! till conj receipt)
    receipt))

(defn sell!
  "Sells `potion` over the counter. Refuses a potion not proven `on-the-shelf`."
  [potion]
  (gate potion #'on-the-shelf 'sell!)
  (ring-up! potion))
```

The gate at the top of `sell!` is a signature gate, where a reader of the function looks first.
The gate in `ring-up!` is an effect gate: the lowest-level write refuses an unproven potion,
even from a caller that skipped `sell!`. A third place, a read gate, lets the fields out only
through a check. The places are not exclusive. The court's sinks, `serve-to-the-queen!` and
`pour-for-the-queen!`, gate on `at-court` in the same two places:

```clojure
(sell! {::name "Draught of Courage" ::recipe {"dragon pepper" 2 "garlic" 1 "honey" 3}})
;; ExceptionInfo: sell! takes only a potion proven on-the-shelf
(sell! relabelled)                ;; => {:sold "Draught of Courage" :pennies 12}
(sell! (into {} relabelled))
;; ExceptionInfo: sell! takes only a potion proven on-the-shelf
(serve-to-the-queen! bottled)
;; ExceptionInfo: serve-to-the-queen! takes only a potion proven at-court
(pour-for-the-queen! bottled)
;; ExceptionInfo: pour-for-the-queen! takes only a potion proven at-court
(serve-to-the-queen! served)      ;; => "Draught of Courage"
```

`bottled` is proven on the shelf, so the court's gates refuse it. The demo's coverage is a test
in `test/recognitum/demo_test.clj`: it hands every public function of `demo.potion` whose name
ends in `!` a plain map and a potion that has passed nothing, and expects each to refuse both.

## Editor support

The library exports a clj-kondo configuration under `resources/clj-kondo.exports`. It teaches
clj-kondo and clojure-lsp the definition forms, and reports most mistakes the macros refuse:
misspelled waits, concerns, inputs and fields, reads outside a check body or inside a function
the body builds, the names the check engine reserves, incomplete `defcopy` maps, a bundle bound
twice in one type, waits that form a cycle, and a checks section after a protocol. It lints
method bodies as clj-kondo lints a `defrecord`'s. It reports nothing in a definition the macros
accept, and may miss a mistake they refuse. The cycles it reports are those of the waits the
forms list and of the fields the bindings name in `:when-extant`; it does not read check
bodies, so a cycle through a field a body reads is reported only by the macros, when the
namespace loads. It sees one form at a time, so a cycle through the waits of a bundle defined
in another namespace is also left to the macros.

The configuration is on the classpath. To import it into a project, make the project's
`.clj-kondo` directory and run `clj-kondo --lint "$(clojure -Spath)" --copy-configs --skip-lint`.

The macros carry `:style/indent` metadata, which CIDER and clojure-lsp read to indent them
(`clojure-lsp format` reads it with `--analysis '{:type :project-and-shallow-analysis}'`).
`defproven` and `defproven-in` indent as `defrecord` does, the other definitions as `defn`
does, and `when-extant` as `when` does. With cljfmt alone, or Calva's formatter, add the
same rules to `.cljfmt.edn`:

```clojure
{:extra-indents {recognitum.core/defproven    [[:block 2] [:inner 1]]
                 recognitum.core/defproven-in [[:block 2] [:inner 1]]
                 recognitum.core/defchecks    [[:inner 0] [:inner 1]]
                 recognitum.core/defcopy      [[:inner 0]]
                 recognitum.core/defconcern   [[:block 1]]
                 recognitum.core/defcontext   [[:inner 0]]
                 recognitum.core/when-extant  [[:block 1]]}}
```

## Running it

```
clojure -X:test                     # the suite, including every file of test/corpus
clojure -M:dev -m demo.heist-run    # the Heist, end to end
clojure -M:dev -m demo.potion-run   # the Potion, end to end
clojure -M:dev -m demo.authz        # refund requests checked against a permission service
clojure -M:dev -m demo.orders       # orders: shapes, invariants, an address bundle bound twice
bb test/corpus/corpus_check.bb      # clj-kondo over the corpus, with the exported hook
```

## License

MIT; see `LICENSE`.
