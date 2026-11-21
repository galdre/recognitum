# recognitum

Types whose values carry proof that their checks passed.

## Install

The library has no Maven or Clojars coordinate. Add it to `deps.edn` as a git dependency:

```text
{:deps {io.github.galdre/recognitum {:git/tag "v0.3.4"}}}
```

A git dependency also needs the sha of its commit. Run `clojure -X:deps git-resolve-tags` once:
it finds the commit of each `:git/tag` in `deps.edn` and adds its `:git/sha`. Then require the
library:

```clojure
(ns casino.heist
  (:require [recognitum.core :as rec]))
```

## What it is

`rec/defproven` defines a type from its fields and its named **checks**, much as `defrecord`
defines a record from its fields. As with a record, the definition gives a class and the
constructors `->T` and `map->T`, an instance of the type is read as a map is (by keyword, by destructuring,
with `keys`), and `assoc` returns a new value of the same class.

Unlike a record, every way to make an instance of the type runs the checks or throws, and every write runs the
checks that read a key it changes. The key of a field is a keyword in the defining namespace:
`:casino.heist/crew`, where a record has `:crew`. A key that is not the key of a field is
refused. So code that holds an instance of the type holds proof that the checks passed on its entries.

An instance of the type is not a record: `record?` is false of it, and it equals a plain map of its entries,
which a record does not.
[docs/reference/names.md](docs/reference/names.md#compared-with-a-record) compares the two
point by point.

A check may ask an outside source, such as a database. When one call of the library checks many
values, the library collects the reads of their checks and calls the source with the keys
together, not once for each value.

`rec/defproven-in` defines a second kind of type, whose values are checked in parts. Its
constructors and writes run no check, and `(rec/seal v sel)` proves a value for one selection of
the checks at a time. [docs/guides/checked-in-parts.md](docs/guides/checked-in-parts.md) works
through an example.

## An example

```clojure
(rec/defproven Heist [crew take cuts]
  rec/checks
  (crew [] "the crew is a set of names" (and (set? crew) (every? string? crew)))
  (take [] "the take is a whole number" (nat-int? take))
  (cuts [] "each cut is a whole number" (and (map? cuts) (every? nat-int? (vals cuts))))

  (cuts-sum-to-take [] "the cuts add up to the take" (= take (reduce + (vals cuts))))
  (only-crew-get-cuts [cuts-sum-to-take] "only the crew gets a cut" (every? crew (keys cuts))))
```

The first vector holds the type's fields. The key of a field is the keyword that has the
field's name in the type's namespace: `:casino.heist/crew`, which code in that namespace writes
as `::crew`. Each clause after `rec/checks` defines a check: its name, a vector of the checks
that must pass before it runs, a docstring, and a body in which the fields are locals. The
check named after a field must also pass before a check that reads the field runs; the vector
need not name it. A check passes when its body returns exactly `true`.

The constructor `map->Heist` runs every check. It returns a `Heist`, or it throws. A **sealed**
value is a value of the current definition of a `rec/defproven` type, and `rec/sealed?` asks
whether its argument is one:

```clojure
(def job (map->Heist {::crew #{"Charlie" "Stella"}
                      ::take 2000
                      ::cuts {"Charlie" 1000 "Stella" 1000}}))

(rec/sealed? job)
;; => true

(map->Heist {::crew #{"Charlie"} ::take 10 ::cuts {"Charlie" 9}})
;; ExceptionInfo: casino.heist/Heist failed 1 check
;;   :casino.heist/cuts-sum-to-take (the cuts add up to the take): false, which blocked :casino.heist/only-crew-get-cuts
```

The message gives one line for each failed check: the check's id (the keyword of the check's
name in the type's namespace), its docstring, what its body returned, and the checks that its
failure kept from running. Code that handles the failure reads the exception's data, which holds
the same facts as a map:

```clojure
(try (map->Heist {::crew #{"Charlie"} ::take 10 ::cuts {"Charlie" 9}})
     (catch clojure.lang.ExceptionInfo e (ex-data e)))
;; => {:error :recognitum/check-failed
;;     :type casino.heist/Heist
;;     :failed {::cuts-sum-to-take {:data false
;;                                  :doc "the cuts add up to the take"
;;                                  :blocked #{::only-crew-get-cuts}}}
;;     :blocked #{::only-crew-get-cuts}}
```

A write to a sealed value (`assoc`, `dissoc`, `conj`, `merge`, `into`) runs the checks that read a key
the write changes. It returns a new value, or it throws as the constructor throws. `assoc` of
several keys, and `merge` of several arguments, are several writes, each checked on its own
result: [docs/reference/writes.md](docs/reference/writes.md) states which calls are one write.

## What it is not

- **It is not a static type system.** The checks run when the program runs: when a sealed value is
  made, and when it is written to.
- **It does not say that a check would pass now.** A sealed value proves that each check passed when
  the check last ran. A check may ask an outside source, such as a database. Nothing runs that
  check again when the source's answer changes, and the value stays sealed.
- **It does not make a function ask for proof.** The library proves a value. It does not know
  which functions need proof. A function that needs a proven `Heist` asks two questions of
  what it is handed, `(instance? Heist x)` and `(rec/sealed? x)`: `rec/sealed?` alone is true
  of a value of any type that `rec/defproven` defined.
- **It does not change data.** A sealed value holds the entries that it was given. The library fills
  in no default and converts nothing.
- **It is not impossible to defeat.** The guarantee is against mistakes, and defeating it is
  hard: each of the two known routes to a sealed value that no check ran on is a deliberate act
  that overrides Java's access rules. One is reflection after `setAccessible`. The other is a
  class defined into the type's own package through the type's own class loader.
  [docs/guarantee.md](docs/guarantee.md#ways-around-the-checks) describes both, and lists the
  routes that are closed.

[docs/guarantee.md](docs/guarantee.md) states what holding a sealed value proves, and each limit in
full.

## How it differs from clojure.spec and Malli

clojure.spec and Malli describe data, and they validate a map when code asks them to. A map
that passed is afterward an ordinary map: nothing ties it to the validation. `rec/defproven`
defines a type. Every way to make an instance of the type runs the type's checks, every write to an instance
runs the checks that read what the write changes, and the instance itself is the evidence that the
checks passed. The libraries are not rivals: a check's body is ordinary Clojure, so it may call
a spec or a Malli validator.

## Stability

Before 1.0, `recognitum.core` may change between minor versions; the [changelog](CHANGELOG.md) lists every
breaking change. The layers below it are unstable and may change in any release.

## Requirements

The library is written for Clojure on the JVM, and its one dependency is Clojure. ClojureScript
and babashka are not supported: the library has no ClojureScript source, and it does not load
in babashka. Its test suite passes on Clojure 1.12.5 with Java 27, and the examples in the
documentation also run on Java 17. On Clojure 1.11.4 the library loads and the example above
runs; the test suite has not been run there. The library does not load on Clojure 1.10.

The library ships a clj-kondo configuration, and its macros carry indentation metadata.
[docs/reference/editor-support.md](docs/reference/editor-support.md) says how to set up both.

Report problems as issues at <https://github.com/galdre/recognitum/issues>.

## Where to go next

| Document | What it holds |
|---|---|
| [docs/tutorial.md](docs/tutorial.md) | A first type, built step by step: a definition, a value, a failure, a write, a draft, and a check that asks an outside source. A new user starts here. |
| [docs/guides/](docs/guides/README.md) | Guides that each work through one task with code that runs, such as building a sealed value in steps, checks that ask a database or a service, sharing checks among types, values that are checked in parts, asking a type's checks about plain data, or testing a type. |
| [docs/reference/](docs/reference/README.md) | The rules that span several functions, one page for each rule. The rules of one function are in its docstring, and the docstring of the namespace `recognitum.core` lists every public function and macro. |
| [docs/guarantee.md](docs/guarantee.md) | What holding a sealed value proves, what establishes that, and what it does not prove. |
| [docs/internals.md](docs/internals.md) | The layers below `recognitum.core`, for a reader who builds on them or contributes to the library. |

These commands need a checkout of the repository, because the dependency holds neither the
tests nor the demos: `git clone https://github.com/galdre/recognitum` makes one.
[docs/internals.md](docs/internals.md) describes `test/corpus` and the exported hook.

```text
clojure -X:test                     # the test suite, including every file of test/corpus
clojure -M:dev -m demo.heist-run    # a longer heist example, printed step by step
bb test/corpus/corpus_check.bb      # clj-kondo over the corpus, with the exported hook
```

## License

MIT; see [LICENSE](LICENSE).
