# When a check runs

A check is a named body of a type's definition that passes by returning exactly `true`. A check
runs only when a call runs it. This page states which checks each call runs, and what decides
whether and when a check runs within the call. One call's execution of checks is a **run**.

## Which checks each call runs

The table uses five terms:

- A **sealed value** is a value of a type that `rec/defproven` defined. It passes every check.
- A **draft** is an unchecked map of such a type, made with `rec/draft`. It remembers the checks
  that pass on its entries.
- A value of a type that `rec/defproven-in` defined also remembers the checks that pass on its
  entries. Nothing checks it but a call that asks to.
- A **selection** (`sel` below) selects some of a type's checks.
- A check **waits** on other checks: it runs only after they have passed.

| Call | Checks it runs |
|---|---|
| `map->T`, `->T` or the tagged literal `#ns/T {...}` of a `rec/defproven` type | Every check of the type. |
| A write (`assoc`, `dissoc`, `conj`, `merge`, `into`) to a sealed value | The checks that read a key the write changes. |
| `(rec/seal d)` of a draft | Every check that `d` does not remember as passing. |
| `(rec/seal v sel)` of a value of a `rec/defproven-in` type | The checks `sel` selects, the checks they wait on, and the shape check of each field that `v` holds or is required to hold, less the checks `v` remembers as passing. |
| `(rec/check x sel)` | The checks `sel` selects and the checks they wait on, less the checks `x` already passes. A sealed value passes every check, so nothing runs. |
| `(rec/recheck x sel)` | The checks `sel` selects, whether or not `x` passes them, and the checks they wait on that `x` does not pass. |
| `rec/check-all`, `rec/recheck-all` | For each value given, what `rec/check` or `rec/recheck` runs. |
| `rec/seal-all` | For each draft and each value of a `rec/defproven-in` type in the shape, what `rec/seal` runs. |
| `rec/probe`, `rec/probe-all` | For each map given, the checks `sel` selects and the checks they wait on. A probe remembers nothing, so every call runs them again. |
| `map->T`, `->T`, the tagged literal or a write, of a `rec/defproven-in` type | None. |
| A write to a draft, `rec/draft`, `rec/clean` | None. |
| `rec/proves?`, `rec/proven-checks`, `rec/proven-concerns`, `rec/checks-of`, `rec/selects-nothing?`, `rec/sealed?`, `rec/draft?` | None. Each answers from what is already known. |

The table is about values and drafts of a type's current definition. A value or a draft of a
**displaced definition**, which is a definition that a later definition of the type replaced,
runs no check: `rec/seal`, `rec/check`, `rec/recheck`, `rec/check-all` and `rec/recheck-all`
throw for it, and one such value or draft among those given to `rec/check-all` or
`rec/recheck-all` makes the call throw before any check runs.
[redefinition.md](redefinition.md) states the rules.

The example type records which bodies run. `in-stock` is a **source**: a function that a body
reads with `rec/fetch`, here the stock on hand of each product.

```clojure
(ns shop.order
  (:require [recognitum.core :as rec]))

(def ran (atom []))

(defn ran!
  "Records that the body `id` ran, and returns `answer`."
  [id answer]
  (swap! ran conj id)
  answer)

(def stock (atom {"tea" 5}))

(defn in-stock [skus] (ran! :in-stock (select-keys @stock skus)))

(rec/defproven Order [sku qty ^:optional gift-note]
  rec/checks
  (sku       [] (ran! :sku (string? sku)))
  (qty       [] (ran! :qty (pos-int? qty)))
  (gift-note [] (ran! :gift-note (string? gift-note)))
  (stocked   [] (ran! :stocked (<= qty (or (rec/fetch in-stock sku) 0))))
  (note-fits [stocked] (ran! :note-fits (rec/when-extant gift-note (< (count gift-note) 40)))))

(defn run-by
  "What ran while `f` was called, sorted."
  [f]
  (reset! ran [])
  (f)
  (sort @ran))
```

A constructor runs every check. The body of `gift-note` does not run here: a check named after
a field is the field's **shape check**, and the shape check of an optional field passes, without
running its body, where the field is absent.

```clojure
(run-by #(map->Order {::sku "tea" ::qty 2}))
;; => (:in-stock :note-fits :qty :sku :stocked)
```

A write runs the checks that read a key it changes. `note-fits` waits on `stocked`, and a write
of the note does not run `stocked`: the value already passes `stocked`, and the write changed
no key that `stocked` reads.

```clojure
(def order (map->Order {::sku "tea" ::qty 2}))

(run-by #(assoc order ::qty 3))
;; => (:in-stock :qty :stocked)
(run-by #(assoc order ::gift-note "For Ada"))
;; => (:gift-note :note-fits)
```

A write to a draft runs nothing, and the seal of the draft runs the checks that the draft does
not remember. The seal leaves the draft remembering every check that passed, so the
`rec/check` after it runs nothing. `rec/recheck` runs the checks that its selection selects,
whether or not the draft remembers them.

```clojure
(def draft (assoc (rec/draft order) ::qty 4))

(run-by #(rec/seal draft))
;; => (:in-stock :qty :stocked)
(run-by #(rec/check draft rec/every))
;; => ()
(run-by #(rec/recheck draft ::stocked))
;; => (:in-stock :stocked)
(run-by #(rec/proves? draft rec/every))
;; => ()
```

## Within one run

- **A check runs only after every check it waits on has passed.** A check waits on the checks
  its clause names in its wait vector, and on the shape check of each field its body reads or
  asks about with `rec/extant?`. A clause may name such a shape check in its wait vector too,
  and naming it changes nothing. Where a check it waits on fails, the check does not run, and
  the report names it under `:blocked`.
- **A check that the value or the draft already passes is not run again for a check that waits
  on it.** The write of the gift note above shows this.
- **A body that runs, runs once for each value, from start to end.** A check that several
  checks wait on runs once, so an effect in a body happens at most once for each value in a
  run.
- **A body sees the dynamic bindings in force where the call was made.** A pass under one
  binding is remembered like any other pass; [memory.md](memory.md) states what follows.
- **Checks that do not wait on one another run in no promised order, and on no promised
  thread.** A body sees the caller's dynamic bindings whatever thread runs it; a body that reads
  a `ThreadLocal` or `Thread/currentThread` may see another thread than the caller's.

Here `qty` fails, so the two checks that wait on it, directly or through `stocked`, do not run:

```clojure
(run-by #(rec/probe Order {::sku "tea" ::qty 0}))
;; => (:qty :sku)
(:blocked (rec/probe Order {::sku "tea" ::qty 0}))
;; => #{::stocked ::note-fits}
```

A body that throws anything but the two failures the library catches (a read of an absent
field, and a failed read from a source) ends the run: the exception propagates out of the call,
as [defproven.md](defproven.md#a-check-body) states.

## Sources

A run that reaches several reads of one source sends them to the source together.
[sources.md](sources.md) states how many calls a source receives.

## The work a call does

The work of a call is the checks in its row of the table and the calls those checks make to
their sources. The repository has a benchmark that times calls of the library against other
code that does the same work, such as a hand-written record with the same checks. To run it in
a checkout of the repository:

```text
clojure -M:bench -e "(require 'recognitum.bench)(recognitum.bench/run)"
```
