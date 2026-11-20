# The guarantee and its limits

This page states what holding a value proves, what establishes that, and what it does not
prove. It is written for a reader who must decide whether to rely on the guarantee.

## The claim

Four terms first. A **check** is a named body in a type's definition that passes by returning
exactly `true`. A check **waits on** the checks that its definition names for it, and on the
check named after each field that its body reads: it runs only after they have passed. A
**sealed value** is a value of the current definition of a type that
`rec/defproven` defined; `(rec/sealed? x)` answers whether `x` is one. A **draft** is an
unchecked map of such a type, made with `rec/draft`.

Two kinds of check pass without running their bodies, where a field marked `^:optional` is
absent from the value: the check named after that field, and each check of a group of checks
that the type binds with `^{:when-extant field}`.
[reference/absence-and-nil.md](reference/absence-and-nil.md) shows both.

**For a type that `rec/defproven` defined:** where `(rec/sealed? x)` is true, `x` holds every
field that is not marked `^:optional`, and every check of the type's current definition has
passed on the entries that `x` holds. A check passed either when `x` was made, or earlier, on a
value or a draft that `x` was made from. In the second case, no write since then has changed a
field that the check reads.

**For a type that `rec/defproven-in` defined:** nothing checks a value of such a type until a
call asks, and such a value is never sealed. Where `(rec/proves? x sel)` is true, `x` holds
every field that is not marked `^:optional`, and these checks passed on exactly the entries
that `x` holds, each when it last ran:

- the checks that `sel` selects, where `sel` is a **selection**, a value that selects some of
  the type's checks;
- the checks that those checks wait on;
- the **shape check** of each field that `x` holds, which is the check named after the field.

**For a draft:** `(rec/proves? d sel)` makes the same claim of a draft `d` as of a value of a
`rec/defproven-in` type, and one more: where it is true, `d` holds no key that its type does
not declare. A draft that proves every check is still not a sealed value, and `rec/sealed?` is
false for it.

All three claims are about the past. None says that a check would pass if it ran now.

```clojure
(ns vault.badge
  (:require [recognitum.core :as rec]))

(def staff (atom #{"Ada" "Grace"}))

(defn on-staff
  "A source: whether each name is on the staff list."
  [names]
  (zipmap names (map #(contains? @staff %) names)))

(rec/defproven Badge [holder level notes]
  rec/checks
  (holder [] "the holder is named" (string? holder))
  (level  [] "the level is 1, 2 or 3" (contains? #{1 2 3} level))
  (notes  [] "the notes are held in an atom" (instance? clojure.lang.Atom notes))
  (employed [] "the holder is on the staff list" (true? (rec/fetch on-staff holder)))
  (few-notes [] "a badge has at most two notes" (<= (count @notes) 2)))

(def badge (map->Badge {::holder "Ada" ::level 2 ::notes (atom [])}))
```

## What establishes the claim for a sealed value

Every way that the library gives to obtain a sealed value runs checks, as this table shows.
[Ways around the checks](#ways-around-the-checks) states what gets past them.

| Way to a value | What runs | What shows it |
|---|---|---|
| `map->T`, `->T` | Every check. The call returns a value or throws. | Tests build values through both and expect a throw for each failing check. |
| The tagged literal `#ns/T {...}`, read from text | Every check: the tag reads through `map->T`. | Tests read a printed value and text that fails a check. |
| A write: `assoc`, `dissoc`, `conj`, `merge`, `into`, or a transient made from the value | The checks that read a key the write changes. The write returns a new sealed value or throws. | Tests count which checks run for each write, and compare each write with the constructor on the same entries. |
| `(rec/seal d)` of a draft | Every check that the draft does not remember as passing. | Tests seal drafts after each kind of write and after failed seals. |
| `rec/seal-all`, `rec/drafting`, `rec/drafting-all` | For each draft that the call seals, what `rec/seal` of that draft runs. | Tests seal drafts that hold drafts, and expect no draft to be sealed where one fails. |
| The class's own constructor, `(T. ...)` | Nothing: it throws `SecurityException`. The constructor takes an access key that only the library holds. | Tests call the constructor without the access key. |
| Anything else that builds a map from the value: `select-keys`, `(into {} v)`, Java deserialization | Nothing, and the result is a plain map, which is not sealed. | The example below; tests serialize a value and read it back. |

```clojure
(Badge. nil {::holder "Mallory" ::level 9})
;; SecurityException: vault.badge.Badge's constructor takes a key only recognitum holds: make a value with vault.badge/map->Badge or vault.badge/->Badge
(rec/sealed? (into {} badge))
;; => false
(= badge (into {} badge))
;; => true
```

The last two lines show that equality is not proof: a plain map equals the sealed value that
has its entries, and proves nothing.

### Why a write runs only some of the checks

A write runs the checks that read a key it changes, and no others. The other checks passed on
entries that the write left as they were. This rests on one fact about check bodies: in a body
the fields are locals, so the library knows from the definition which fields each check reads.
A check whose answer depends on something that is not a field of the value is covered by the
limits below.

### What a draft remembers

A draft remembers which checks passed on its entries, so that a seal need not run them again.
The memory cannot be forged through the public API. Only two things put a check into a
draft's memory: a run of the check that returned `true` on the draft's entries, and
`rec/draft` of a sealed value, which gives a draft that remembers every check. A write to a
draft (`assoc`, `dissoc`, `conj`, `merge`, `into`) returns a draft that remembers what the
draft written to remembers, less each check that reads a key the write changes. So a write
adds no check to a memory. Metadata holds none of the memory: `with-meta` neither adds a check
nor removes one.

Tests build memories by hand with the library's internals: a memory moved onto other
entries, and a memory that names as its proof another value, the entries themselves, or a draft
on which no check ran. Each such draft proves nothing and fails to seal. Tests also give a
draft a key that its type does not declare, by each kind of write, and expect `rec/proves?` to
be false until the key is gone.
[reference/memory.md](reference/memory.md) states the rules of the memory.

## What the proof does not cover

### A source that would answer differently now

A **source** is a function that a check body reads with `rec/fetch`, such as a query of a
database. A check that reads a source judged the entries against the answer that the source
gave when the check ran. The value stays sealed when the source's answer changes.
`(rec/recheck x sel)` runs the checks that `sel` selects again, whether or not `x` has passed
them. It answers `true`, or a **report**: a map that holds each failed check under `:failed`. It
does not unseal the value.

```clojure
(swap! staff disj "Ada")

(rec/sealed? badge)
;; => true
(:failed (rec/recheck badge ::employed))
;; => {::employed {:data false :doc "the holder is on the staff list" :blocked #{}}}
(rec/sealed? badge)
;; => true
```

### A binding that was in force when a check ran

A check body sees the dynamic bindings, and the `with-redefs`, in force when it runs. A value
that was made under one binding stays sealed outside it, and a draft that passed a check under
a binding remembers the pass. `with-redefs` on a source is therefore a way to seal a value
against an answer that the real source never gave.
[reference/memory.md](reference/memory.md) shows a draft that passes a check under a binding,
and [reference/sources.md](reference/sources.md) shows a value made under `with-redefs`.

### A function that a check body calls, defined again later

A check judged the entries with the functions that its body called when the check ran. Where
such a function is defined again and now answers differently, the values made before stay
sealed, and the type's definition is not displaced. `rec/recheck` runs the checks with the
function as it is now.

### A mutable object in a field

The checks run on the entries. Where an entry is a mutable object, such as an atom or a Java
array, a later change inside the object runs no check, and the value stays sealed. A write of
another key does not run the checks that read the changed object either.

```clojure
(swap! staff conj "Ada")
(swap! (::notes badge) into ["late" "lost" "found"])

(rec/sealed? badge)
;; => true
(rec/sealed? (assoc badge ::level 3))
;; => true
(:failed (rec/recheck badge ::few-notes))
;; => {::few-notes {:data false :doc "a badge has at most two notes" :blocked #{}}}
```

A type whose proof must hold keeps immutable data in its fields.

### `true` from `rec/check`

`(rec/check x sel)` answers `true` where no selected check fails. That is not proof, for two
reasons:

- It answers `true` where `sel` selects nothing in the type of `x`, since nothing ran.
- It does not read a key that a draft holds and the draft's type does not declare. So it can
  answer `true` for a draft that `rec/seal` refuses.

The two questions that answer for proof are `rec/sealed?` and `rec/proves?`. `rec/proves?` is
false for a draft while the draft holds such a key.

### A value of a `rec/defproven-in` type that is an instance of its class

Every value of a `rec/defproven-in` type is an instance of the type's class and implements its
protocols, whatever it has passed. For such a type `instance?` proves nothing, and
`rec/sealed?` is always false. The only question that answers for proof is
`(rec/proves? x sel)`, and it answers for one selection at a time: a value proven by one
selection may fail another.

`(rec/seal v sel)` and `(rec/proves? v sel)` refuse a selection that selects nothing in the
type of `v`: the seal throws and `rec/proves?` is false. A **concern** is a mark that a check
carries as a flag, and a concern is a selection of the checks that carry it. The refusal
catches one mistake, and only in part: a check that was meant to carry a concern, and lost its
flag. The mistake is caught only where no other check of the type carries that concern. Where
another check does, the concern selects that other check, and the seal runs it and not the
check that lost its flag.

## Redefinition

Evaluating a type's definition again makes a new class, and the values of the earlier
definition are no longer sealed. `rec/sealed?` and `rec/proves?` answer false for them wherever
they are asked. A write that changes one throws, and so does a method that the definition
lists, other than `toString`. `rec/seal`, `rec/check`, `rec/recheck`, `rec/check-all` and
`rec/recheck-all` throw for one too, and for a draft of the earlier definition: none of them
runs a check of the earlier definition, and none answers `true` for such a value or draft. Two
things still accept such a value:

- **`instance?` against the earlier class.** Code that already ran `(instance? T x)` before the
  redefinition keeps the earlier class, and its test stays true of the earlier values. A
  function that must refuse an unproven value across a redefinition asks `(rec/sealed? x)` as
  well as `(instance? T x)`.
- **A protocol extended to the class from outside the definition**, with `extend-protocol` or
  `extend-type`. Such a method is not guarded, and still answers for the earlier values.

[reference/redefinition.md](reference/redefinition.md) states every case.

## Ways around the checks

| Way | Closed or open |
|---|---|
| Calling the class's constructor | Closed: it throws without the type's access key. |
| Printing a value and reading the text, or editing the text first | Closed: the tag reads through `map->T`, which runs every check. |
| Java serialization | Closed: a value is written as a plain map, and comes back as one. |
| Metadata | Changes no entry, so it opens nothing. Whether `with-meta` on a value returns a sealed value is not promised. |
| The fourth argument of `rec/probe`. A **probe** asks a type's checks about a plain map, and its fourth argument answers in a source's place for that call | Closed: a probe builds no value and remembers nothing, so no value proves a check that passed under it. |
| `with-redefs` on a source, or a dynamic binding that a body reads | Open, as stated above. |
| Java reflection that overrides access checks (`setAccessible`), or a class defined into the type's package | Open. The type's access key is a `static final` field of the class, with package access. Two kinds of code can read it: code that reads the field by reflection after `setAccessible`, and a class that is defined into the type's own package through the type's own class loader. Either can then call the constructor with any entries, and the result is a sealed value that no check ran on. Both are deliberate acts that override Java's access rules, and the library does not guard against them. |
| Calling the layers below `recognitum.core` directly (`recognitum.record`, `recognitum.proof`) | Outside this page, which states the guarantee of `recognitum.core` only. |

The guarantee is against mistakes. Defeating it on purpose is hard, and not impossible: of the
ways that this page covers, only the two routes of the row on reflection give a sealed value
that no check ran on, and each is a deliberate act that overrides Java's access rules. The
other open way, a `with-redefs` or a binding, runs the checks, and changes what they see.

## Checks that throw, and two threads

- **A check body that throws.** A read of an absent field, and a failed read from a source,
  fail the check. Any other exception from a body, and an `Error` from a source, propagate out
  of the call that ran the check. That call returns no value, so no value is sealed by a run
  that threw.
- **Two threads that check one draft at once.** Tests cover the case where a `rec/check` or a
  `rec/check-all` finds a pass, a `rec/recheck` on another thread then finds the same check
  failing, and the first run finishes last: the draft does not remember the pass. They also
  cover a `rec/recheck` or a `rec/check-all` that finds a failure and finishes after another
  run: the draft forgets the failed check. No test covers two threads on one value of a
  `rec/defproven-in` type, and no docstring promises anything about concurrent runs.

## What the caller must do

The library proves a value. It does not know which functions need proof. Asking for proof is
left to the code that uses the library, in three parts:

1. **Ask in the function that acts.** A function whose effect depends on the checks (a sale, a
   write, a payment) asks two questions of the value it is handed, and refuses the value
   unless both are true. The first asks for the type: `(instance? T x)`. The second asks for
   the proof: `(rec/sealed? x)` where `rec/defproven` defined `T`, and `(rec/proves? x sel)`,
   with the selection that the function needs, where `rec/defproven-in` defined `T`. The second
   question does not ask for the type: `rec/sealed?` is true of a sealed value of any type,
   and `(rec/proves? x sel)` can be true of a value of another type, and of a draft, as
   [reference/selections.md](reference/selections.md) states. Only the code that receives a
   value can refuse one without proof. [guides/sinks.md](guides/sinks.md) shows such
   functions.
2. **Ask right before acting.** The proof is a fact about the past. Where a source may have
   changed and that matters, the function calls `rec/recheck` first.
3. **Cover every such function.** Neither a value nor a function can see the rest of the code.
   That every function with an effect has its question is for a test or a lint to show; the
   library provides neither. The repository's own example is a test that hands every public
   function of `demo.potion` whose name ends in `!` a plain map and a value that has passed
   nothing, and expects each to refuse both (`test/recognitum/demo_test.clj`).

The sections above leave the caller four more duties:

- **Take neither equality nor `true` from `rec/check` for proof.** A plain map equals the
  sealed value that has its entries, as
  [the example above](#what-establishes-the-claim-for-a-sealed-value) shows, and
  [`rec/check` answers `true` in two cases that prove nothing](#true-from-reccheck).
- **Keep immutable data in the fields** of a type whose proof must hold:
  [a change inside a mutable object runs no check](#a-mutable-object-in-a-field).
- **Make no value, and check no draft, under `with-redefs` on a source or under a binding
  that a check body reads**, unless the proof is meant to rest on the answer given there:
  [the value stays sealed outside it](#a-binding-that-was-in-force-when-a-check-ran).
- **Ask in a method that is extended to a type's class from outside the definition.** Such a
  method is not guarded, and after [a redefinition](#redefinition) it still answers for the
  earlier values, so it asks `(rec/sealed? x)` itself where it needs proof.

## Stability

Before 1.0, `recognitum.core` may change between minor versions; the [changelog](../CHANGELOG.md) lists every
breaking change. The layers below it are unstable and may change in any release.
