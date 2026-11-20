# Tutorial: a first type

This tutorial builds one type, the plan of a heist, in the order in which a new user meets the
library: a definition, a value, a value that fails, a write, a draft, and a check that asks an
outside source. It assumes a working knowledge of Clojure, and a REPL that has the library on
its classpath. Each step gives forms to evaluate, shows what comes back, and says why. In the
examples, a comment `;; => x` shows the value of the form before it, and a comment
`;; ExceptionInfo: ...` shows the message of what the form throws.

[The README](../README.md#install) says how to add the library to a project. To get the REPL:

1. Put the README's entry in the `deps.edn` of a directory.
2. Run `clojure -X:deps git-resolve-tags` in that directory, once.
3. Run `clj` in that directory, or start a REPL for the project from an editor.

The commands under [Where to go next](#where-to-go-next) run the library's demos. They need a
checkout of the repository, because the dependency does not hold the demos.

## 1. Require the library

```clojure
(ns caper.heist
  (:require [clojure.string :as str]
            [recognitum.core :as rec]))
```

This tutorial starts a new example in a namespace of its own. Its `Heist` has one field more
than the `Heist` of the README, and it needs nothing that the README's example defined.

Every example in the documentation uses the alias `rec`. The examples below are written in this
namespace, so `::take` is the keyword `:caper.heist/take`. A REPL prints such a keyword in full.

## 2. Define a type

```clojure
(rec/defproven Heist [name crew take cuts]
  rec/checks
  (name [] "the job has a name" (and (string? name) (not (str/blank? name))))
  (crew [] "the crew is a set of names" (and (set? crew) (every? string? crew)))
  (take [] "the take is a whole number" (nat-int? take))
  (cuts [] "each cut is a whole number" (and (map? cuts) (every? nat-int? (vals cuts))))

  (cuts-sum-to-take [] "the cuts add up to the take" (= take (reduce + (vals cuts))))
  (only-crew-get-cuts [cuts-sum-to-take] "only the crew gets a cut" (every? crew (keys cuts))))
```

The vector holds the type's **fields**. Each form after `rec/checks` defines a **check**: a
name, a vector that step 5 explains, a docstring, and a body.

- In a body, the fields are locals. A field's name hides a var of the same name there: in the
  bodies above, `name` and `take` are the fields, not the functions of `clojure.core`.
- A check passes when its body returns exactly `true`. Anything else that the body returns,
  such as `false`, `nil` or a string, fails the check.
- A check named after a field is that field's **shape check**: it says what the field may
  hold. The last two checks state rules that span fields.

The form defines the class `Heist` and two constructors, `map->Heist` and `->Heist`.

## 3. Make a value

`map->Heist` takes a map from each field's key to its value. A field's key is the keyword, in
the namespace of the definition, that has the field's name.

```clojure
(def job
  (map->Heist {::name "The Italian Job"
               ::crew #{"Charlie" "Stella"}
               ::take 2000
               ::cuts {"Charlie" 1000 "Stella" 1000}}))

(::take job)
;; => 2000
(= job (->Heist "The Italian Job" #{"Charlie" "Stella"} 2000 {"Charlie" 1000 "Stella" 1000}))
;; => true
(rec/sealed? job)
;; => true
```

A constructor runs every check, and returns a value or throws. So a value is proof that every
check passed on its entries, and `(rec/sealed? x)` asks whether `x` is such a value. `->Heist`
takes every field in order.

A value reads, compares and hashes as a map of its entries. At a REPL it prints as a tagged
literal, which is shortened here:

```text
#caper.heist/Heist #:caper.heist{:name "The Italian Job", :crew #{"Stella" "Charlie"}, ...}
```

[reference/printing-and-reading.md](reference/printing-and-reading.md) says how to read that
text back.

## 4. A value that fails

Here the cuts add up to 9, and the take is 10:

```clojure
(map->Heist {::name "Job" ::crew #{"Charlie"} ::take 10 ::cuts {"Charlie" 9}})
;; ExceptionInfo: caper.heist/Heist failed 1 check
;;   :caper.heist/cuts-sum-to-take (the cuts add up to the take): false, which blocked :caper.heist/only-crew-get-cuts
```

The message gives one line for each failed check: the check's id, its docstring, what its body
returned, and the checks that its failure kept from running. A check's id is the keyword, in
the namespace of the definition, that has the check's name.

Code that handles a failure reads the exception's data, not its message. The function
`failure` below returns that data, and the later steps use it:

```clojure
(defn failure
  "The data of what `map->Heist` throws for `entries`, or nil where it returns a value."
  [entries]
  (try (map->Heist entries) nil
       (catch clojure.lang.ExceptionInfo e (ex-data e))))

(failure {::name "" ::crew #{"Charlie"} ::take 10 ::cuts {"Charlie" 9}})
;; => {:error :recognitum/check-failed
;;     :type caper.heist/Heist
;;     :failed {::name {:data false :doc "the job has a name" :blocked #{}}
;;              ::cuts-sum-to-take {:data false
;;                                  :doc "the cuts add up to the take"
;;                                  :blocked #{::only-crew-get-cuts}}}
;;     :blocked #{::only-crew-get-cuts}}
```

One throw names every failed check, because the constructor runs every check that can run.
Under `:failed`, `:data` is what the check's body returned. A field that is left out is named
under `:missing`:

```clojure
(:missing (failure {::name "Job" ::crew #{"Charlie"} ::take 10}))
;; => #{::cuts}
```

[reference/failures.md](reference/failures.md) states everything that a failure holds.

## 5. Checks that wait on other checks

A check **waits** on other checks: it runs only after they have passed. Where one of them
fails, the check does not run, and the failure names it under `:blocked`. A check waits on two
kinds of check:

- The shape check of each field that its body reads. The clause does not name these: the
  library finds them in the body.
- Each check that its clause names in the vector after its name. Above, `only-crew-get-cuts`
  names `cuts-sum-to-take`.

So a body may rely on the shapes of the fields that it reads. Here the take is not a number.
The shape check of `take` fails, and `cuts-sum-to-take` never tries to add the cuts up to a
string:

```clojure
(let [{:keys [failed blocked]} (failure {::name "Job" ::crew #{"Charlie"} ::take "lots"
                                         ::cuts {"Charlie" 9}})]
  [(keys failed) blocked])
;; => [(::take) #{::cuts-sum-to-take ::only-crew-get-cuts}]
```

## 6. Change a value

A value is written to as a map is: with `assoc`, `dissoc`, `conj`, `merge`, `into`, and the
functions built on them, such as `update`. A write runs the checks that read a key it changes.
It returns a new value, or throws as the constructor throws. The value that was written to is
unchanged.

```clojure
(rec/sealed? (assoc job ::name "The Bank Job"))
;; => true
(assoc job ::take 3000)
;; ExceptionInfo: caper.heist/Heist failed 1 check
;;   :caper.heist/cuts-sum-to-take (the cuts add up to the take): false
(::take (merge job {::take 3000 ::cuts {"Charlie" 1500 "Stella" 1500}}))
;; => 3000
```

The second write fails because a write is checked on its own result, and a take of 3000 does
not match the old cuts. The third write changes the take and the cuts together: `merge` of one
map is one write, and so is `into`. `assoc` of several keys is one write for each key.

A value refuses a key that is not the key of one of its type's fields:

```clojure
(assoc job ::car "Mini")
;; ExceptionInfo: caper.heist/Heist has no field :caper.heist/car. Its fields: :caper.heist/name :caper.heist/crew :caper.heist/take :caper.heist/cuts
```

[reference/writes.md](reference/writes.md) states which checks each write runs.

## 7. Build a value in steps

Some values are built over several steps, and are not valid until the last one. A **draft** is
an unchecked map of a type, and it accepts any write. `(rec/draft Heist)` makes a draft that
holds nothing. `(rec/seal d)` runs the checks on the draft `d`, and returns the value or throws
as the constructor throws. A seal also throws for a key that is not the key of one of the
type's fields, as the write to a value does in step 6; it never drops such a key.
`(rec/clean d)` returns the draft without those keys, for code that means to drop them.

```clojure
(def draft
  (-> (rec/draft Heist)
      (assoc ::name "The Bank Job")
      (assoc ::crew #{"Charlie" "Stella"})
      (assoc ::take 3000)))

(rec/seal draft)
;; ExceptionInfo: caper.heist/Heist failed 1 check and lacks the required field :caper.heist/cuts
;;   :caper.heist/cuts (each cut is a whole number): {:absent :caper.heist/cuts}, which blocked :caper.heist/cuts-sum-to-take, :caper.heist/only-crew-get-cuts
(rec/proven-checks draft)
;; => #{::name ::crew ::take}

(def bank-job (rec/seal (assoc draft ::cuts {"Charlie" 1500 "Stella" 1500})))

(rec/sealed? bank-job)
;; => true
```

The first line of the message says that the draft lacks `cuts`, a field that every `Heist` must
hold. The second line is the failure of the check `cuts`: a check that reads an absent field
fails with the data `{:absent key}`, where `key` is the field's key.

A draft remembers the checks that passed on its entries. The failed seal left the draft
remembering three checks, which `rec/proven-checks` lists, so the second seal ran only the
other three. A write to a draft makes the new draft forget the checks that read a key the
write changes.

`(rec/draft job)` opens a value as a draft that holds the value's entries. That is the way to
take a value through several writes when the states in between are not valid.
[guides/drafts.md](guides/drafts.md) shows more, and how to seal many drafts together.

## 8. Add to the type

The plan now gets a getaway driver, and the house that pays for the job must have vetted the
crew. The definition is evaluated again, with one more field and three more checks. Step 9
explains `^:optional` and `rec/when-extant`, and step 10 explains `rec/fetch-each`.

```clojure
(defn vetted
  "For each name, whether the house has vetted that person."
  [names]
  (zipmap names (map #(contains? #{"Charlie" "Stella" "Handsome Rob"} %) names)))

(rec/defproven Heist [name crew take cuts ^:optional getaway]
  rec/checks
  (name [] "the job has a name" (and (string? name) (not (str/blank? name))))
  (crew [] "the crew is a set of names" (and (set? crew) (every? string? crew)))
  (take [] "the take is a whole number" (nat-int? take))
  (cuts [] "each cut is a whole number" (and (map? cuts) (every? nat-int? (vals cuts))))
  (getaway [] "the getaway driver is named" (and (string? getaway) (not (str/blank? getaway))))

  (cuts-sum-to-take [] "the cuts add up to the take" (= take (reduce + (vals cuts))))
  (only-crew-get-cuts [cuts-sum-to-take] "only the crew gets a cut" (every? crew (keys cuts)))
  (getaway-not-crew [] "the driver stays out of the vault"
    (rec/when-extant getaway (not (contains? crew getaway))))
  (crew-vetted [] "the house has vetted everyone on the crew"
    (every? true? (vals (rec/fetch-each vetted crew)))))
```

Evaluating a definition again makes a new class. The values that were made before belong to
the earlier definition, and they are no longer proof of anything. They still read as maps. A
write to one throws, and so does `rec/check` or `rec/seal` of one. The message of the throw
gives the way back: `(rec/seal (rec/draft v))` runs the checks of the new definition on the
entries of such a value `v`, and returns a value of the new definition:

```clojure
(rec/sealed? job)
;; => false

(def job (rec/seal (rec/draft job)))

(rec/sealed? job)
;; => true
```

[guides/repl.md](guides/repl.md) says what else changes when a definition is evaluated again.

## 9. An optional field

A field marked `^:optional` may be absent from a value. Every other field is required. Absent
means that the value has no entry under the field's key. A field that holds `nil` is present.

```clojure
(contains? job ::getaway)
;; => false
(::getaway (assoc job ::getaway "Handsome Rob"))
;; => "Handsome Rob"
(assoc job ::getaway nil)
;; ExceptionInfo: caper.heist/Heist failed 1 check
;;   :caper.heist/getaway (the getaway driver is named): false, which blocked :caper.heist/getaway-not-crew
(assoc job ::getaway "Charlie")
;; ExceptionInfo: caper.heist/Heist failed 1 check
;;   :caper.heist/getaway-not-crew (the driver stays out of the vault): false
```

- The shape check of an optional field passes where the field is absent. Where the field holds
  `nil`, the shape check runs on `nil`. So code that means "no driver" leaves the key out, or
  removes it with `dissoc`.
- In a check body, a read of an absent field fails the check. `getaway-not-crew` reads an
  optional field, so it asks first: `(rec/when-extant getaway body...)` runs the body where the
  field is present, and passes where the field is absent.

[reference/absence-and-nil.md](reference/absence-and-nil.md) states the rules of absent fields.

## 10. A check that asks a source

`crew-vetted` cannot judge the crew from the plan alone: it asks the house. A **source** is a
function that takes a vector of distinct keys and returns a map from each key to its answer.
`vetted` is one. A check body reads one key from a source with `(rec/fetch source k)`. It reads
several keys with `(rec/fetch-each source ks)`, which returns a map from each key to its answer.

```clojure
(assoc job ::crew #{"Charlie" "Stella" "Steve"})
;; ExceptionInfo: caper.heist/Heist failed 1 check
;;   :caper.heist/crew-vetted (the house has vetted everyone on the crew): false
```

A body does not call the source itself. One call of the library, such as a constructor or a
write, runs several checks. The library collects the reads of those checks, and calls the
source with the keys of all of them. So where one call of the library checks many values, a
source that queries a database is queried for all of them together.
[guides/sources.md](guides/sources.md) shows this.

A check that reads a source judges the plan by the answer that the source gives when the check
runs. Nothing runs the check again when the answer changes: `job` stays sealed if the house
later strikes Charlie from its list.
[guarantee.md](guarantee.md) states what a value proves and what it does not.

## Where to go next

In a checkout of the repository (`git clone https://github.com/galdre/recognitum`),
`clojure -M:dev -m demo.heist-run` runs a longer version of this example and prints each step.
Its source is `dev/demo/heist.clj`.

The rules of one function are in its docstring: `(clojure.repl/doc rec/seal)`. The docstring of
the namespace `recognitum.core` lists every public function and macro.

Each guide works through one task:

| Task | Guide |
|---|---|
| Build values in steps, or seal many together | [guides/drafts.md](guides/drafts.md) |
| Write checks that ask a database or a service | [guides/sources.md](guides/sources.md) |
| Ask a type's checks about plain data, and report every mistake at once | [guides/asking-without-building.md](guides/asking-without-building.md) |
| Share one group of checks among several types | [guides/bundles.md](guides/bundles.md) |
| Check a value in parts, where different code asks different checks of it | [guides/checked-in-parts.md](guides/checked-in-parts.md) |
| Make a function refuse a value that lacks proof | [guides/sinks.md](guides/sinks.md) |
| Give a type the methods of a protocol or an interface | [guides/methods.md](guides/methods.md) |
| Test a type and the code that uses it | [guides/testing.md](guides/testing.md) |
| Work at a REPL, where definitions are evaluated again | [guides/repl.md](guides/repl.md) |

[reference/README.md](reference/README.md) lists the pages that state one rule each in full,
and [guarantee.md](guarantee.md) states what holding a value proves, and what it does not.
