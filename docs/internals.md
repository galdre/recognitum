# Internals: the layers below `recognitum.core`

Before 1.0, `recognitum.core` may change between minor versions; the [changelog](../CHANGELOG.md) lists every
breaking change. The layers below it are unstable and may change in any release.

This page is for a reader who calls `recognitum.record`, `recognitum.engine` or
`recognitum.proof` directly, or who changes the library. For that reader, the second sentence
above covers everything this page names outside `recognitum.core`: every function, protocol,
class, and key of a map. Any release may rename, change or remove any of them. Code that calls
one of them is written against one release of the library.

The page has three parts:

- the map: [the layers, and which may depend on which](#the-layers-and-which-may-depend-on-which);
- each layer, from the top down: [`recognitum.core`](#recognitumcore-the-wiring),
  [the record layer](#the-record-layer), with
  [how to define a type without the macros](#defining-a-type-without-the-macros),
  [the check engine](#the-check-engine-and-how-it-batches-reads), and
  [the proof layer](#the-proof-layer), with
  [what a strategy guarantees](#what-every-proof-strategy-guarantees),
  [what another strategy would implement](#what-another-proof-strategy-would-implement) and
  [why `recognitum.proof` is never reloaded](#why-recognitumproof-is-never-reloaded);
- what holds across the layers: [the limits of a type's size](#the-limits-of-a-types-size) and
  [the working rules for a contributor](#working-rules-for-a-contributor).

## The examples on this page

Every block of Clojure on this page runs, in order, in one namespace. A test evaluates the
blocks and compares each result with the comment that shows it:
[how the code blocks are kept true](#how-the-code-blocks-of-the-readme-and-of-docs-are-kept-true)
describes the test. A comment `;; => x` gives the value of the form before it. A comment
`;; ExceptionInfo: message` gives the class and the message of what the form before it throws.
The namespace is this one:

```clojure
(ns internals.examples
  (:require [recognitum.engine :as engine]
            [recognitum.engine.runner :as runner]
            [recognitum.engine.waves :as waves]
            [recognitum.proof :as proof]
            [recognitum.proof.key-class :as key-class]
            [recognitum.record :as record]
            [recognitum.record.types :as types]
            [recognitum.record.values :as values]))
```

## The layers, and which may depend on which

The library has three layers and, above them, one namespace that joins them. `design/layers.edn`
is the authority: it names, for each namespace, the namespaces of this project that it may
depend on.

| Layer | Namespace | Its work | It may depend on |
|---|---|---|---|
| The public API | `recognitum.core` | The macros and functions that a user calls. It chooses the proof strategy and the check engine, and hands both to the record layer. | Any namespace below. |
| The record layer | `recognitum.define` | What `defproven` and `defproven-in` expand to. | `recognitum.body`, `recognitum.define.checks`, `recognitum.define.clauses`, `recognitum.define.methods`, `recognitum.record`, `recognitum.record.types`, `recognitum.record.values`, `recognitum.record.views` |
| | `recognitum.define.checks` | A type's checks: its own clauses compiled and the checks its bundle bindings bring. | `recognitum.body`, `recognitum.define.bundles`, `recognitum.define.clauses`, `recognitum.define.methods`, `recognitum.record` |
| | `recognitum.define.methods` | The sections of methods: protocols, interfaces, hints, and each method's function. | `recognitum.body`, `recognitum.define.clauses` |
| | `recognitum.define.bundles` | What `defchecks`, `defcopy` and `defconcern` expand to, and the bundle values they build. | `recognitum.body`, `recognitum.define.clauses`, `recognitum.select` |
| | `recognitum.define.clauses` | What a definition's symbols name, one clause of checks with its flags, and the refusals every defining form shares. | `recognitum.body`, `recognitum.record.probe` |
| | `recognitum.record` | Defines a type from compiled checks: its type map, its installed write and the handle that holds its access key. | `recognitum.proof`, `recognitum.record.draft`, `recognitum.record.memory`, `recognitum.record.probe`, `recognitum.record.reports`, `recognitum.record.runs`, `recognitum.record.types`, `recognitum.record.values`, `recognitum.record.views`, `recognitum.select` |
| | `recognitum.record.walk` | Seals, or opens as drafts, the values that a walk of a nested shape reaches. | `recognitum.proof`, `recognitum.record.draft`, `recognitum.record.reports`, `recognitum.record.runs`, `recognitum.record.selection`, `recognitum.record.types`, `recognitum.record.values`, `recognitum.select` |
| | `recognitum.record.runs` | Runs the checks a selection names in one value or in many, in one run of the engine. | `recognitum.record.draft`, `recognitum.record.memory`, `recognitum.record.probe`, `recognitum.record.reports`, `recognitum.record.selection`, `recognitum.record.types`, `recognitum.record.values`, `recognitum.select` |
| | `recognitum.record.selection` | What a selection asks of a type: the checks it selects with the presence checks of the required fields, and whether it selects nothing. | `recognitum.select` |
| | `recognitum.record.values` | Makes, drafts, cleans and seals a value of any type through its type's write, and says what a value is known to pass. | `recognitum.proof`, `recognitum.record.draft`, `recognitum.record.memory`, `recognitum.record.reports`, `recognitum.record.selection`, `recognitum.record.types`, `recognitum.select` |
| | `recognitum.record.views` | What a write's checks read in place of the map the write makes, and the forms of a type's guards. | `recognitum.proof` |
| | `recognitum.record.draft` | The draft: an unchecked map that forgets, at each write, the checks that read a key written. | `recognitum.record.memory` |
| | `recognitum.record.memory` | What a draft or a value of an unsealed type remembers, and the checks its memory shows passing. | `recognitum.proof` |
| | `recognitum.record.types` | The type a value, a draft or a class belongs to, whether a definition is current, and how values and drafts print. | `recognitum.proof`, `recognitum.record.draft`, `recognitum.record.memory`, `recognitum.select` |
| | `recognitum.record.probe` | Runs a type's checks on plain maps, with some sources answered by overrides. | `recognitum.proof`, `recognitum.record.draft`, `recognitum.record.reports`, `recognitum.record.selection`, `recognitum.record.types`, `recognitum.select` |
| | `recognitum.record.reports` | The reports of a run of checks, and the record layer's refusals. | `recognitum.select` |
| | `recognitum.body` | Reads one check body when a macro expands. | Nothing. |
| | `recognitum.select` | Selections, and which checks a selection selects in a type. | Nothing. |
| The check engine | `recognitum.engine` | Compiles check bodies, and makes an engine from checks. | `recognitum.engine.rewrite`, `recognitum.engine.runner`, `recognitum.engine.runtime`, `recognitum.engine.step` |
| | `recognitum.engine.waves` | Runs engines over a group of values, in waves. | `recognitum.engine.runtime`, `recognitum.engine.step` |
| | `recognitum.engine.runner` | Runs some checks of an engine on one value at a time. | `recognitum.engine.runtime`, `recognitum.engine.step` |
| | `recognitum.engine.step` | The engine, and one step of a check's body, which every run shares. | `recognitum.engine.runtime` |
| | `recognitum.engine.rewrite` | Rewrites a body that reads a source into a form that can stop at a read and resume. | `recognitum.engine.runtime` |
| | `recognitum.engine.runtime` | What a compiled body calls when it runs. | Nothing. |
| The proof layer | `recognitum.proof` | The protocol between the record layer and a proof strategy. | Nothing. |
| | `recognitum.proof.key-class` | The one proof strategy that the library has. | `recognitum.proof`, `recognitum.proof.key-class.analysis`, `recognitum.proof.key-class.changes`, `recognitum.proof.key-class.emit` |
| | `recognitum.proof.key-class.analysis` | What defining a definition takes, or why the strategy refuses it. | `recognitum.proof` |
| | `recognitum.proof.key-class.changes` | What a value's changes call in place of its write: the net change as pairs, which holds no access key. | Nothing. |
| | `recognitum.proof.key-class.emit` | The bytecode of the classes the key-class strategy defines. | `recognitum.proof` |

Three consequences of the table:

- The record layer names no proof strategy and no check engine. `recognitum.record` depends on
  the protocol `recognitum.proof` and never on `recognitum.proof.key-class` or
  `recognitum.engine`. It receives a strategy and an engine's functions as arguments.
- The check engine depends on nothing outside itself. It knows checks, values as maps, and
  sources, and it knows nothing of types or of proof.
- The proof layer depends on nothing outside itself. It knows nothing of checks.

`recognitum.core` is the only namespace of the library that may name a concrete strategy or a
concrete engine. `design/layers.edn` lists it under `:wiring`. The file also lists the demos,
the benchmarks and every test namespace, each with the namespaces that it may depend on. Only
the demos, the benchmarks and the tests may depend on `recognitum.core`: no layer may.

A namespace **depends on** another when it requires that namespace, names one of its vars by a
qualified symbol (in a quoted or syntax-quoted form too), or imports a class that the other
namespace defines.

The test `recognitum.layers-test` holds the code to the file. It reads every `.clj` file under
`src`, `dev`, `bench` and `test/recognitum`, and it fails in four cases:

- a namespace has a dependency that the file does not allow;
- a namespace is not named in the file;
- the file lists, under `:to-fix`, a dependency that the code no longer has (`:to-fix` holds
  the forbidden dependencies that the code has and that are to be removed);
- the file names more than two namespaces under `:wiring`.

So a contributor who adds a namespace, or a dependency that the file does not allow, changes
`design/layers.edn` in the same commit. Where a namespace names a qualified keyword of a
namespace that it does not depend on, the test prints a line that begins `layers: knowledge:`
and does not fail.

To run this test alone:

```text
clojure -X:test :nses '[recognitum.layers-test]'
```

## `recognitum.core`: the wiring

`recognitum.core` holds two private maps, and they are the whole of the connection between the
layers:

- `wiring` names the proof strategy (`recognitum.proof.key-class/strategy`) and three functions
  of the engine: `recognitum.engine/define`, `recognitum.engine.waves/run-all` and
  `recognitum.engine.runner/runner`. The form that a defining
  macro emits passes this map to `recognitum.record/define-type`.
- `expansion` holds what a defining macro needs while it expands: the engine's
  `recognitum.engine/body-form`, which compiles a check body; the macros that a body may call
  to read (`rec/fetch`, `rec/fetch-each`, `rec/extant?`, `rec/when-extant`); the symbol
  `rec/checks`, which starts a section of checks in a definition; and the strategy, which
  answers the name of a type's class and refuses a definition that it cannot make.

Each defining macro of `recognitum.core` calls a function of `recognitum.define` (`defproven`,
`defproven-in`) or of `recognitum.define.bundles` (`defchecks`, `defcopy`, `defconcern`). Most of the
other public functions call the function of the same name in a child of `recognitum.record`:
`recognitum.record.values` (`draft`, `clean`, `seal`, `sealed?`, `proves?`, `proven-checks`,
`proven-concerns`, `checks-of`, `selects-nothing?`), `recognitum.record.runs` (`check`,
`recheck`, `check-all`, `recheck-all`), `recognitum.record.probe` (`probe`, `probe-all`),
`recognitum.record.draft` (`draft?`) and `recognitum.record.walk` (`seal-all`, `drafting-all`,
`drafting`); and the selections are those of `recognitum.select`.

Both maps are private. The library has no public way to choose another strategy or another
engine: to use another one is to change this namespace.

## The record layer

`recognitum.record` gives a type its meaning: which checks a constructor, a write, a seal and
a probe run, what a draft remembers, and what a redefinition does to the values of the earlier
definition. The docstring of the namespace states the terms, and the docstring of each
function states its rules. The pages under [reference/](reference/README.md) state the same
rules in the form in which a user of `recognitum.core` meets them.

The layer has three other namespaces. The first two work when a macro expands:

- `recognitum.define` and its children parse the form of each defining macro, refuse the
  mistakes that they can see, and emit one form that calls `recognitum.record/define-type`.
- `recognitum.body` expands the macros of one check body and finds what the body reads. It
  returns the body with each read written as the engine reads it: `(&field k)` for a field,
  `(&extant? k)` to ask whether a field is present, and `(&fetch source key)` and
  `(&fetch-each source keys)` for a source.
- `recognitum.select` holds the selections, and works out which checks a selection selects
  in a type. `recognitum.record` calls it when a function is given a selection.

### Defining a type without the macros

`(recognitum.record/define-type spec wiring)` defines a type and returns a map that describes
it. This map is **the type**: the functions of `recognitum.record` take it, or find it from a
value, a draft or a class.

`wiring` names the proof strategy and three functions of the engine. `recognitum.core` passes
this strategy and these functions. The aliases `key-class`, `engine` and `record` are those of
[the namespace of this page's examples](#the-examples-on-this-page):

```clojure
(def wiring
  {:strategy key-class/strategy
   :define   engine/define
   :run-all  waves/run-all
   :runner   runner/runner})
```

`spec` names the type, its fields and its checks. A field has its key, the symbol that names
it, and whether it is optional. A check has these keys:

- `:id`, the keyword that names the check;
- `:run`, a compiled check, which the paragraph after this list describes;
- `:shape-of`, only on a shape check: the key of its field;
- `:reads`, the keys that the check's body reads;
- `:waits`, the ids of the checks that the check waits on;
- `:fetches? true`, only where the check's body reads a source. `define-type` runs the checks
  without this flag in a way that calls no source. A check that reads a source without the
  flag therefore throws when it runs, with a message that ends "reads a source, and a runner
  calls none".

A **compiled check** is the value of the form that `recognitum.engine/body-form` returns.
`body-form` takes a body in which every macro is already expanded and every read is written
as the engine reads it: `(&field k)`, `(&extant? k)`, `(&fetch source key)` or
`(&fetch-each source keys)`. It returns a form, not a function, so a macro calls it and
places the form in its expansion:

```clojure
(defmacro compiled
  "The compiled check of `body`, a form with no macro in it."
  [body]
  (engine/body-form body))
```

The definition of a type with three fields, a shape check for two of them, and one more check:

```clojure
(def Reading
  (record/define-type
   {:name   'internals.examples/Reading
    :fields [{:key :station :sym 'station :optional? false}
             {:key :celsius :sym 'celsius :optional? false}
             {:key :note    :sym 'note    :optional? true}]
    :checks [{:id :station :shape-of :station :waits #{} :reads #{:station}
              :run (compiled (string? (&field :station)))}
             {:id :celsius :shape-of :celsius :waits #{} :reads #{:celsius}
              :run (compiled (number? (&field :celsius)))}
             {:id :above-absolute-zero :waits #{} :reads #{:celsius}
              :run (compiled (< -273.15 (&field :celsius)))}]}
   wiring))
```

`define-type` adds, to the checks that a check waits on, the shape check of each key that the
check reads. So `:above-absolute-zero` waits on `:celsius`, although its `:waits` is empty:

```clojure
(get-in Reading [:by-id :above-absolute-zero :waits])
;; => #{:celsius}
```

`recognitum.record.values/make` is what `map->T` calls. It runs every check and returns a sealed
value, or throws:

```clojure
(def reading (values/make Reading {:station "north" :celsius 21.5}))

(values/sealed? reading)
;; => true
(identical? Reading (types/type-of reading))
;; => true
(values/make Reading {:station "north" :celsius 1 :wind 3})
;; ExceptionInfo: internals.examples/Reading has no field :wind. Its fields: :station :celsius :note
```

A write to the value is checked, as a write to a value of a `rec/defproven` type is:

```clojure
(values/sealed? (assoc reading :note "calm"))
;; => true
(assoc reading :celsius "warm")
;; ExceptionInfo: internals.examples/Reading failed 1 check
;;   :celsius: false, which blocked :above-absolute-zero
```

A draft is made from the type's class, which `recognitum.record.values/value-class` answers:

```clojure
(def draft (assoc (values/draft (values/value-class Reading)) :station "south" :celsius 3))

(values/sealed? draft)
;; => false
(values/sealed? (values/seal draft))
;; => true
```

`define-type` does less than `rec/defproven`. The macro's expansion also does these things,
and code that calls `define-type` directly does without them or does them itself:

- It imports the type's class into the namespace under the type's name, and defines `map->T`
  and `->T`. After the definition above, `Reading` is the var that the example made, and the
  namespace has no `map->Reading`:

  ```clojure
  (resolve 'map->Reading)
  ;; => nil
  ```

- It writes each source that a body reads as `(recognitum.record.probe/sourced source)`. This is how
  an override of `rec/probe` answers in a source's place: a check that reads its source
  without `sourced` always reads the source itself.
- It refuses, when the macro expands, a definition whose interfaces or methods the proof
  strategy would refuse when the type is defined. Where the definition fails later, it removes
  the vars that the definition's form interned.
- It passes `:guard` and `:change`, two forms that give each type code of its own for its
  checked writes. Types defined without them share the code that `define-type` holds for
  checked writes.
- It passes `:instead`, a string. The constructor of the type's class throws when code
  without the access key calls it, and its message closes with this string, which tells the
  caller what to call instead of the constructor.

The docstring of `define-type` lists every key of the spec, among them `:interfaces` and
`:methods` for protocols and interfaces, `:unsealed true` for a type as `rec/defproven-in`
defines one, and `:gate` for a check that passes without running while a field is absent.

Defining a type under a name that already names a type is a redefinition, as it is with the
macros. [reference/redefinition.md](reference/redefinition.md) states what follows for the
values, drafts and constructors of the earlier definition.

## The check engine, and how it batches reads

The docstring of `recognitum.engine` names four functions for a caller: `body-form` and `define` of
`recognitum.engine`, `run-all` of `recognitum.engine.waves` and `runner` of
`recognitum.engine.runner`:

- `(body-form body)` returns the form of a compiled check, as
  [Defining a type without the macros](#defining-a-type-without-the-macros) shows.
- `(define checks)` makes an **engine** from a map `{id {:after #{id ...} :body check}}`.
  `:after` holds the ids of the checks that this check waits on. `define` throws where a check
  waits on an id that the map lacks, and where the waits form a cycle.
- `(run-all items)` runs a group. Each item is `[engine value assumed]`: `value` is a map
  from key to field value, and `assumed` is a collection of ids. A check in `assumed` counts as passed
  and does not run. `run-all` returns one result for each item, in order:
  `{:failed {id failure} :blocked #{id ...}}`.
- `(runner engine ids)` returns a function of a value and a set of assumed ids. That function
  runs the checks that `ids` names, one after another on the calling thread, and calls no
  source: where a check reaches a read of a source, the call throws. The record layer uses a
  runner for the checks that a spec does not mark `:fetches? true`, and `run-all` where a
  check to run has the mark.

A **source** is a function that takes a vector of distinct keys and returns a map from key to
answer.

### Waves

One call of `run-all` is a **run**. A run proceeds in waves:

1. Every check that can start runs until it finishes or reaches a read whose answer the run
   does not have. At such a read the check **parks**: it stops, and the run keeps what the
   check asked for.
2. When no check can go on, the run calls each source once, with every key that a parked check
   asked of that source and that the run has not asked before.
3. The parked checks resume with the answers, and the next wave begins.

Batching changes how the sources are called and never what a check answers: each check answers
what it would answer if each of its reads called its source immediately, with its one key.

Within one run, the docstring of `recognitum.engine` promises three things:

- A source is asked for a key at most once, so each call passes distinct keys.
- A source is asked for a key exactly where a check that runs reaches a read of that key.
- A source is called no more times than the longest chain of reads has links. A chain runs
  along a path of waits (a check, then a check that waits on it, and so on), and each `&fetch`
  or `&fetch-each` on the path is one link.

The run compares sources with `=`. Reads of one source therefore share its calls across the
checks of one value, across the values of one group, and across the engines of one group.

The example has two sources, and each records the keys of every call it receives. Three
orders are checked as one group. The check `:supplied` reads `supplier-of`. The check
`:approved` reads `supplier-of` and then reads `approved?` with the answer, so its chain of
reads has two links.

```clojure
(def calls (atom []))

(defn supplier-of [skus]
  (swap! calls conj [:supplier-of (set skus)])
  (zipmap skus (map {"tea" "acme" "jam" "bolt"} skus)))

(defn approved? [suppliers]
  (swap! calls conj [:approved? (set suppliers)])
  (zipmap suppliers (map #(= "acme" %) suppliers)))

(def orders
  (engine/define
   {:sku      {:after #{}     :body (compiled (string? (&field :sku)))}
    :supplied {:after #{:sku} :body (compiled (some? (&fetch supplier-of (&field :sku))))}
    :approved {:after #{:sku}
               :body (compiled (true? (&fetch approved? (&fetch supplier-of (&field :sku)))))}}))

(waves/run-all [[orders {:sku "tea"} #{}]
                 [orders {:sku "jam"} #{}]
                 [orders {:sku "tea"} #{}]])
;; => [{:failed {} :blocked #{}}
;;     {:failed {:approved false} :blocked #{}}
;;     {:failed {} :blocked #{}}]
```

The three values made six reads of `supplier-of` and three of `approved?`. Each source received
one call, with the distinct keys:

```clojure
@calls
;; => [[:supplier-of #{"tea" "jam"}] [:approved? #{"acme" "bolt"}]]
```

A check in `assumed` does not run, so its reads are not made. A value whose every check is
assumed calls no source:

```clojure
(reset! calls [])
(waves/run-all [[orders {:sku "tea"} #{:sku :supplied :approved}]])
;; => [{:failed {} :blocked #{}}]
@calls
;; => []
```

### What a check's failure is

A check passes when its body returns exactly `true`. Otherwise it fails, with one of three
kinds of failure data:

- what the body returned;
- `{:absent key}`, where the body read a field that the value lacks;
- `{:fetch-failed source :cause exception}`, where a read of a source failed.

A read fails in two cases. Where a source threw an `Exception`, the read of every key of that
call fails. Where the source's map holds a `Throwable` as the answer for a key, the reads of
that key fail. A key that the source's map leaves out reads as `nil`. An absent field and a failed read are ordinary exceptions inside the body,
which the body may catch. Anything else that a body throws propagates out of `run-all`, which
then returns nothing for any item. An `Error` that a source throws propagates too.

Where a check fails, each check that waits on it is **blocked**: it does not run, and the
result names it under `:blocked`.

```clojure
(waves/run-all [[orders {} #{}]])
;; => [{:failed {:sku {:absent :sku}} :blocked #{:supplied :approved}}]
```

## The proof layer

`recognitum.proof` is two protocols, `Strategy` and `Handle`, two interfaces, and three helper
functions. The terms:

- A **proof strategy** is an implementation of the protocol `Strategy`. It defines types.
- One call of `(proof/define-type strategy type-name definition)` is one **definition** of a
  type. It makes a class for the type's values, a class for its drafts and an **access key**,
  and it returns a **handle**: an object that holds the access key and implements the protocol
  `Handle`.
- A value is **proven under a handle** when `(proof/proven? handle value)` is true.
- A **write** is a function that the holder of a handle installs once, with
  `proof/install-write!`. A **guard** is a function for the writes of one key, and a **change
  guard** is a function for every other change; both are installed with the write.

Every function that needs the access key takes the handle. So the caller keeps the access key
only by keeping the handle. `recognitum.record/define-type` keeps the handle in a closure and
never in a var, and the type that it returns holds no access key.

The proof layer runs no check. `proof/seal` proves whatever map it is given:

```clojure
(def handle (proof/define-type key-class/strategy 'internals.examples/Pair {:keys [:left :right]}))

(def pair (proof/seal handle {:left 1 :right 2}))

(proof/proven? handle pair)
;; => true
(proof/proven? handle {:left 1 :right 2})
;; => false
(= pair {:left 1 :right 2})
;; => true
```

That a sealed value has passed its checks is the work of the record layer, which calls `seal`
only after the checks have passed and installs a write that runs the checks.

With no write installed, a change of a proven value gives a plain map, which is proven under
no handle:

```clojure
(proof/proven? handle (assoc pair :left 5))
;; => false
```

With a write installed, `assoc`, `dissoc`, `conj`, `merge` and `into` on a proven value call
the write, which returns a sealed value or throws. The write here accepts a map whose `:left`
is a number. Its two-argument arity serves `conj`, `merge` and `into`, and its four-argument
arity serves `assoc` and `dissoc`:

```clojure
(defn write
  ([old entries]
   (if (number? (:left entries))
     (proof/seal handle entries)
     (throw (ex-info ":left is not a number" {}))))
  ([question _ _] nil)
  ([old entries k v] (write old entries)))

(proof/install-write! handle write)

(proof/proven? handle (assoc pair :left 5))
;; => true
(assoc pair :left "five")
;; ExceptionInfo: :left is not a number
```

The write also needs its three-argument arity. Once `recognitum.record` is loaded, printing a
proven value calls the installed write with three arguments, to ask whether
`recognitum.record/define-type` defined the value's type; `recognitum.record.types/type-of` and
`recognitum.record.values/sealed?` do the same. This write answers `nil`, so the value prints as its
map. A write without the arity throws `ArityException` each time a value is printed:

```clojure
(pr-str (assoc pair :left 5))
;; => "{:left 5, :right 2}"
```

A second definition under the same name is a redefinition. A value of the earlier definition is
not proven under the new handle:

```clojure
(def handle-2 (proof/define-type key-class/strategy 'internals.examples/Pair {:keys [:left :right]}))

(proof/proven? handle-2 pair)
;; => false
```

### What every proof strategy guarantees

The docstring of [`recognitum.proof`](../src/recognitum/proof.clj) lists what every strategy
guarantees, and it is the full statement. In short:

- **The ways to a proven value.** A value is proven under a handle only if `seal` made it with
  that handle, or the write installed on that handle accepted it, or a guard or the change
  guard installed with that write returned for the change.
- **Changes.** `assoc`, `dissoc`, `conj`, `merge` and `into` on a proven value each make one
  call: of the installed write, or of a guard where one is installed. An `assoc` or a `dissoc`
  that alters nothing may return the value itself and call nothing. With no write installed,
  every change that alters a value gives a map that is not proven. `empty` throws.
- **A value of a definition is a map.** It keeps one field for each key that its definition declares, and
  answers as the plain map of its entries. It prints as its map, and the text never reads
  back as a proven value.
- **Redefinition.** `define-type` again with the same name is a redefinition. The values of
  the earlier definition are not proven under the new handle, and they keep the methods of
  their own definition.
- **Classes.** The value class of every definition implements `recognitum.proof.Proven`, an
  interface with no methods, so one entry in a multimethod such as `print-method` serves the
  values of every definition. The value class and the draft class of a definition each have a
  public static method `gate()`. It returns what `proof/installed` returns for that
  definition: a function that calls the write installed on the definition, or `nil` where no
  write is installed. `proof/gate-of` calls the `gate()` of a class.
- **Unsealed definitions.** A definition made with `:unsealed true`, as `rec/defproven-in`
  makes one, is **unsealed**. `proven?` is false of its values under every handle, and its
  handle seals nothing and installs no write. Its handle builds values that hold a **memory**,
  an object that `proof/memory` reads without the handle, and installs a **carry**, a function
  that each change of a value calls.

One thing is not guaranteed: that `with-meta` keeps proof. `seal` takes the metadata of the map
that it seals, so a caller sets metadata before it seals.

The record layer adds to the printing. `recognitum.record` gives `recognitum.proof.Proven` a
`print-method` entry. For a value whose type `recognitum.record/define-type` defined, the
entry prints the tag of the type before the map. The `reading` of the record layer's example
prints so:

```clojure
(pr-str reading)
;; => "#internals.examples/Reading {:station \"north\", :celsius 21.5}"
```

These guarantees hold against code that does not hold the access key.
[The guarantee and its limits](guarantee.md) states what they do not hold against, such as
reflection that overrides access checks.

### What another proof strategy would implement

A second strategy would implement these, and the docstrings in `recognitum.proof` state the
rules of each:

- **The protocol `Strategy`**:
  - `define-type` defines a type and returns its handle.
  - `refusal` answers, without defining anything, the refusal that `define-type` would throw
    for a definition; the macros call it when they expand. So a strategy refuses a definition
    at two stages. At the first, the macro expands, and it throws the refusal that `refusal`
    answers. At the second, the type is defined, and `define-type` asks again. The second
    answer can differ from the first, because a refusal depends on the classes that the names
    of the listed interfaces load and on the entries of `print-method` and `print-dup`, and
    code that runs between the two stages can change either. A `define-type` that refuses
    defines nothing, and an earlier definition of the type stays current.
  - `class-name` answers the name of the class of a type's values, which is the same under
    every definition of the type.
  - `marked?` answers, without a handle, whether a draft that the strategy opened records a
    check as passed.
  - `installed` answers, for a value class, a function that calls the write installed on the
    definition of that class, or `nil` where no write is installed.
  - `memory` answers the memory that a value of an unsealed definition holds.
  - `removed` answers the object that an installed write receives in place of a value, where
    a `dissoc` removes a key.
- **The protocol `Handle`**, on the object that `define-type` returns:
  - `seal` makes a proven value from a map.
  - `build` makes a value of an unsealed definition from a map and a memory.
  - `proven?` answers whether a value is proven under the handle.
  - `install-write!` installs the write, with or without guards.
  - `install-carry!` installs the carry, on the handle of an unsealed definition.
  - `open`, `mark!` and `passed?` are the proof of a draft. `open` makes a draft with no
    marks, `mark!` marks a check as passed on a draft, and `passed?` answers whether a check is
    marked as passed on a draft.
  - `classes` answers the value class and the draft class.
  - `capabilities` answers the objects that hold the access key, so that a test can confirm
    that no loaded var holds one.
- **The guarantees that the docstring of `recognitum.proof` lists.** Two of them are about
  classes and are outside the protocols: the static method `gate()` on the value class and on
  the draft class, and the interface `recognitum.proof.Proven` on the value class. The values
  of an unsealed definition also implement `recognitum.proof.Built`, whose one method answers
  the value's memory.

`recognitum.proof` has two helpers for a strategy. `checked-transient` gives a transient whose
`persistent!` makes one call of a write, so that `into` is one checked write. `plain-map` gives
the entries and metadata of a map as a plain persistent map.

To put a second strategy to use, `recognitum.core` would name it in place of
`recognitum.proof.key-class/strategy`, and `design/layers.edn` would list its namespace. No
namespace of the record layer would change for it: the record layer reaches a strategy only
through `recognitum.proof`.

`test/recognitum/key_class_test.clj`, in the main suite, tests the key-class strategy. It
tests that one strategy by name, so a second strategy would need tests of its own.

### Why `recognitum.proof` is never reloaded

The docstring of `recognitum.proof` says never to reload the namespace. So do not evaluate
`(require 'recognitum.proof :reload)`.

Evaluating the namespace again makes new protocols and new interfaces under the old names.
The handles, the values and the strategy made before the reload implement the old ones. After
`(require 'recognitum.proof :reload)` in a JVM that held a type, a handle and a value, three
things failed:

- A call of a protocol function on the earlier handle, in code compiled after the reload,
  threw `IllegalArgumentException`, with a message that begins "No implementation of method:
  :proven? of protocol: #'recognitum.proof/Handle". A call of `proof/define-type` on the
  strategy threw in the same way.
- `(instance? recognitum.proof.Proven value)`, compiled after the reload, was false of a value
  made before the reload.
- A type that `rec/defproven` defined after the reload gave values that printed as plain maps,
  without the tag of their type.

The rest of what was tried went on working. Code compiled before the reload still called the
earlier handle. The value made before the reload was still sealed, and a write to it was
still checked. The type defined after the reload gave sealed values, and a write to one of
them was checked.

The docstring's rule covers `:reload-all` too, which reloads every namespace that the named
namespace requires, directly or through another. `(require 'recognitum.core :reload-all)`
reloads `recognitum.proof` and, with it, every other namespace of the library. After that
form, in a JVM that held a type and a value, one of the three failures was seen: the
`instance?` test, compiled after the reload, was false of the value made before the reload.
That value was still sealed, a write to it was still checked, and it still printed with its
tag. A type defined after the reload gave sealed values that printed with their tag.

`recognitum.proof.key-class` holds no access key: the handles hold them. Its docstring states
that reloading it loses nothing. After `(require 'recognitum.proof.key-class :reload)` in a JVM
that held a type and a value, the value was still sealed, a write to it was still checked, and
a type defined afterward gave sealed values that printed with their tag.

## The limits of a type's size

**A type has at most 250 fields.** This is the one limit of size for which a user's definition
is refused. The key-class strategy refuses a definition that declares more keys, with the
refusal kind `:too-many-keys`. A `rec/defproven` form with more fields throws when it is evaluated, and
defines nothing. The limit comes from the class: the value class has a constructor that takes
every field, and the JVM limits the number of a constructor's parameters.

The strategy also refuses an `:instead` of more than 10000 characters. `:instead` is the text
that the constructor of the class shows, and `recognitum.define` writes it, so a user's
definition does not reach this limit.

The library refuses no definition for the number of its checks.

Three sizes change how the code represents a type, without changing what the type does. Past
each of them, a type runs code that a smaller type does not run, so a test on a small type
does not cover it:

- **More than 20 fields.** A Clojure function takes at most twenty fixed parameters, so the
  `->T` of a wider type takes the fields past the twentieth as its rest arguments. It still
  requires exactly one argument for each field. `test/recognitum/wide_test.clj` covers such
  types.
- **More than 64 checks.** For a type of at most 64 checks, `recognitum.record` keeps the set
  of checks that a draft or a value passes as the bits of one `long`, beside the set itself.
  For a larger type it keeps the set alone.
- **More than 160 fields.** The key-class strategy lays out the methods of a class of more
  than 160 keys in another way, which the docstring of `recognitum.proof.key-class` describes.

## Working rules for a contributor

### Running the tests

```text
clojure -X:test
```

This command runs the main suite: every namespace under `test` whose name ends in `-test`.
The suite includes the tests that hold `design/layers.edn`, the files of `test/corpus`, the
README's examples, the examples under `docs/` and the demos, each described below. To run
some namespaces alone, name them:

```text
clojure -X:test :nses '[recognitum.docs-test recognitum.layers-test]'
```

### `test/corpus` and the lint configuration

`test/corpus` holds one small file for each form that the macros accept or refuse. The comment
at the head of each file holds, after the word `expect`, a map that states what the file must
produce: no report, or a report at a given line and column that names a given token. The files
are in three directories: `usage` holds namespaces that use the library correctly, `mistakes`
holds one file for each mistake, and `extra` holds further cases of both kinds.

Two programs read the corpus. The first holds the macros to the headers, and the second holds
the lint configuration to them:

- **The macros.** `recognitum.corpus-test`, in the main suite, loads every `.clj` file of the
  corpus but one, which holds mistakes that only a linter reports. A file whose header expects
  no report must load. A file whose header expects a mistake must fail to load with a message
  that names a token of the header. Where the macros only warn about the mistake, the file
  must load and print a warning that names the token.
- **The lint configuration.** The library exports a clj-kondo configuration and a hook under
  `resources/clj-kondo.exports/recognitum/recognitum`. The script
  `test/corpus/corpus_check.bb` runs clj-kondo with that configuration over the corpus and
  compares what clj-kondo reports with each header. It needs `bb` (babashka) and `clj-kondo`
  on the path, and the main suite does not run it:

  ```text
  bb test/corpus/corpus_check.bb
  ```

Each program fails when a header no longer matches what the program finds. So a contributor
who changes what a macro accepts, or the token that a message names, changes the corpus in
the same commit. The hook
must report nothing in a definition that the macros accept; it may miss a mistake that they
refuse. [reference/editor-support.md](reference/editor-support.md) states what the lint
reports and misses.

### What each layer promises, and the tests that hold it to that

The docstring of a layer's namespace states what the layer promises to the code that calls it,
and the docstring of each function states that function's rules. The tests of the main suite
hold the code to them:

| Layer | Its promises are stated in the docstrings of | Tests |
|---|---|---|
| The proof layer | `recognitum.proof`, and each method of its two protocols | `recognitum.key-class-test` |
| The check engine | `recognitum.engine` and its four functions, in it and its children | `recognitum.engine-test` |
| The record layer | `recognitum.record` and its functions | The other namespaces under `test/recognitum`. Most of them call the layer through `recognitum.core`. |
| The dependencies between the layers | `design/layers.edn` | `recognitum.layers-test` |

### How the code blocks of the README and of `docs/` are kept true

Two tests of the main suite run the code that the documents show.

**`recognitum.docs-test`** runs every document under `docs/`, this page among them. The
docstring of [the test](../test/recognitum/docs_test.clj) states its rules for a document in
full. A writer of a page meets these first:

- Every fenced block is marked `clojure` or `text`. A `clojure` block runs. A `text` block
  holds what is not code to run, such as a command or a message.
- The `clojure` blocks of one file run in order, in the namespace that the file's first block
  declares with an `ns` form. No loaded namespace may have that name.
- A result is shown as `;; => x`, and a throw as `;; SomeException: message`, as
  [the examples on this page](#the-examples-on-this-page) show them. A result or a throw in
  any other spelling fails the test, since nothing would compare it.

**`recognitum.readme-test`** runs the README by the same rules: every `clojure` block of
`README.md`, in order, in the namespace that the README's first block declares. The test also
fails where the README has no `clojure` block. It holds no text of the README, so a block that
is reworded needs no change to the test.

A new page under `docs/` needs no change to a test: `recognitum.docs-test` finds it.

### The demos

`dev/demo` holds four worked examples. Each has a program that runs it from start to end:

```text
clojure -M:dev -m demo.heist-run
clojure -M:dev -m demo.potion-run
clojure -M:dev -m demo.authz
clojure -M:dev -m demo.orders
```

`recognitum.demo-test` and `recognitum.walkthrough-test`, in the main suite, run the four
programs and check what they print.

### The benchmark

`bench/recognitum/bench.clj` holds a list of rows. Each row is one call of the library and the
same work on a hand-written `defrecord`. The benchmark prints, for each row, the time of the
hand-written side, the time of the library, and the second divided by the first:

```text
clojure -M:bench -e "(require 'recognitum.bench)(recognitum.bench/run)"
```

A second benchmark runs `recognitum.engine` against an engine that calls a source once for
each read, and prints the times and the number of calls of the sources:

```text
clojure -M:bench -e "(require 'recognitum.engine-bench)(recognitum.engine-bench/run)"
```

### Formatting

The project formats its code with cljfmt, under the rules of `.cljfmt.edn`, which also names
the directories that are formatted:

```text
clojure -M:fmt check
clojure -M:fmt fix
```

`check` reports each file that is not formatted, and `fix` rewrites those files. Run `check`
before a commit: it is expected to report no file.

### Prose

The project holds every string that a person reads to one standard: docstrings, comments, the
messages of exceptions and of assertions, `testing` strings, and the names of functions,
bindings, keywords and fixtures. Its main rules:

- A docstring is the contract for the caller: what the function does, takes, returns and
  throws. What describes the implementation goes in a comment at the line that it explains.
- Each fact is stated once.
- A text uses no term that its reader cannot understand from the text, and none that names a
  plan, a date, a person or an earlier state of the code.
- The message of an exception is in plain words and holds the data that its reader needs to
  act.
