# What drafts and values of a `rec/defproven-in` type remember

Two kinds of thing remember the checks that passed on their entries:

- a **draft**, an unchecked map of a `rec/defproven` type, made with `rec/draft`;
- a value of a `rec/defproven-in` type, whose constructors and writes check nothing.

What either remembers is a fact about the past: each remembered check returned `true` when it
last ran on these entries. Nothing runs a remembered check again but a call that asks to.

A sealed value, which is a value of a `rec/defproven` type, passes every check of its type. Its
proof is a fact about the past in the same way: each check returned `true` the last time a
constructor or a write ran it.

`rec/proves?` and `rec/proven-checks` run nothing. `rec/proven-checks` returns the ids of the
checks that are remembered. `rec/proves?` answers from the memory and from the entries: it is
false while a required field is absent, and false while a draft holds a key that its type does
not declare, whatever is remembered.

```clojure
(ns depot.parcel
  (:require [recognitum.core :as rec]))

(def served-towns (atom #{"Oslo" "Bergen"}))

(defn served [towns] (zipmap towns (map #(contains? @served-towns %) towns)))

(def ^:dynamic *limit-kg* 30)

(rec/defproven Parcel [to kg]
  rec/checks
  (to [] "the town is named" (string? to))
  (kg [] "the weight is a positive number" (and (number? kg) (pos? kg)))
  (deliverable [] "the depot serves the town" (true? (rec/fetch served to)))
  (liftable [] "the weight is within the limit" (<= kg *limit-kg*)))
```

`served` is a **source**: a function that a check body reads with `rec/fetch`. The examples
below pass a **selection**, a value that selects some of a type's checks: `rec/every` selects
every check, `rec/shape` selects the checks named after fields, and `(rec/fetching served)`
selects the checks that read `served`.

## What a memory starts with

| Made by | Remembers |
|---|---|
| `(rec/draft T)`, given the type's class | Nothing. |
| `(rec/draft v)`, given a sealed value | Every check. |
| `map->T`, `->T` or the tagged literal of a `rec/defproven-in` type | Nothing. |
| A write to a draft or to a value of a `rec/defproven-in` type | What the draft or the value that was written to remembered, less the checks that read a key the write changes. |

## What adds to a memory and what removes from it

`rec/check`, `rec/recheck`, `rec/check-all`, `rec/recheck-all`, `rec/seal` and `rec/seal-all`
run checks. After each of them, the draft or the value remembers each check that passed and no
longer remembers a check that failed. A seal that fails does the same, so the next seal runs
only the checks that are left.

The memory is written in place: every holder of the draft, or of the value, sees what a run
wrote. A write is different. It returns a new draft or a new value, and the one written to
remembers what it remembered before.

```clojure
(def draft (into (rec/draft Parcel) {::to "Oslo" ::kg 12}))

(rec/proven-checks draft)
;; => #{}
(rec/check draft rec/shape)
;; => true
(rec/proven-checks draft)
;; => #{::to ::kg}

(def heavier (assoc draft ::kg 20))

(rec/proven-checks heavier)
;; => #{::to}
(rec/proven-checks draft)
;; => #{::to ::kg}
```

A run changes the memory only for the checks that it ran. So after a check fails,
the memory can still hold a check that waits on the failed one. `rec/proven-checks` lists that
check, and `rec/proves?` by it is false, because `rec/proves?` also asks for the checks that
the selected checks wait on. Here `short-route` waits on `served-town`:

```clojure
(rec/defproven Route [town stops]
  rec/checks
  (town  [] (string? town))
  (stops [] (pos-int? stops))
  (served-town [] "the depot serves the town" (true? (rec/fetch served town)))
  (short-route [served-town] "the route has fewer than five stops" (< stops 5)))

(def route (into (rec/draft Route) {::town "Bergen" ::stops 2}))

(rec/check route rec/every)
;; => true
(swap! served-towns disj "Bergen")
(true? (rec/recheck route ::served-town))
;; => false
(rec/proven-checks route)
;; => #{::town ::stops ::short-route}
(rec/proves? route ::short-route)
;; => false
(swap! served-towns conj "Bergen")
```

## What does not remove from a memory

A change outside the entries removes nothing from a memory. None of these makes a draft or a
value forget:

- a source that would now answer differently;
- a dynamic binding, or a `with-redefs`, that was in force when the check ran and is not in
  force now;
- a change inside a mutable object that a field holds, such as an atom.

`rec/check` skips a remembered check, and so does a seal. `(rec/recheck x sel)` runs the checks
`sel` selects whether or not `x` remembers them; it is the call to make when a source's answer
may have changed.

```clojure
(rec/check draft rec/every)
;; => true
(swap! served-towns disj "Oslo")

(rec/proves? draft rec/every)
;; => true
(rec/check draft rec/every)
;; => true
(:failed (rec/recheck draft (rec/fetching served)))
;; => {::deliverable {:data false :doc "the depot serves the town" :blocked #{}}}
(rec/proves? draft rec/every)
;; => false
```

A sealed value is in the same position. It stays sealed, `rec/check` of it runs nothing, and
`rec/recheck` of it runs the selected checks and answers their report. The value stays sealed
whatever the report says:

```clojure
(swap! served-towns conj "Oslo")
(def parcel (map->Parcel {::to "Oslo" ::kg 12}))
(swap! served-towns disj "Oslo")

(rec/sealed? parcel)
;; => true
(true? (rec/recheck parcel (rec/fetching served)))
;; => false
(rec/sealed? parcel)
;; => true
```

A pass under a binding is remembered like any other pass. Here the draft passes `liftable`
under a raised limit, and then seals outside the binding without running `liftable` again:

```clojure
(swap! served-towns conj "Oslo")
(def crate (into (rec/draft Parcel) {::to "Oslo" ::kg 50}))

(binding [*limit-kg* 100] (rec/check crate rec/every))
;; => true
(rec/sealed? (rec/seal crate))
;; => true
(map->Parcel {::to "Oslo" ::kg 50})
;; ExceptionInfo: depot.parcel/Parcel failed 1 check
;;   :depot.parcel/liftable (the weight is within the limit): false
```

`with-redefs` on a source, or on a function that a body calls, has the same effect, and it also
replaces the var for every thread while it is in force. To ask a type's checks with another
answer from a source, without any memory of the result, use the fourth argument of
`rec/probe`: [sources.md](sources.md) describes it.

## A key the type does not declare

A draft accepts a key that its type does not declare, and no check reads the entry under such
a key. While a draft holds one:

- `rec/proves?` of the draft is false, whatever it is asked and whatever the draft remembers,
  since `rec/seal` would refuse the draft;
- `rec/proven-concerns` returns the empty set, since it answers as `rec/proves?` judges each
  concern;
- the memory is kept, and `rec/proven-checks` returns it;
- `rec/check` and `rec/recheck` run and answer as for any draft, and do not report the key.

Once the key is gone, removed by `rec/clean` or by `dissoc`, `rec/proves?` answers by the
memory again, and nothing runs.

```clojure
(def tagged (into (rec/draft Parcel) {::to "Oslo" ::kg 12 ::tag "fragile"}))

(rec/check tagged rec/every)
;; => true
(rec/proven-checks tagged)
;; => #{::to ::kg ::deliverable ::liftable}
(rec/proves? tagged rec/every)
;; => false
(rec/proves? (rec/clean tagged) rec/every)
;; => true
(rec/proves? (dissoc tagged ::tag) rec/every)
;; => true
```

A value of a `rec/defproven-in` type never holds such a key: its constructors and its writes
throw for one.

## After a redefinition

A **displaced definition** is a definition of a type that a later definition replaced. A value
or a draft of a displaced definition proves nothing, whatever it remembered: `rec/proves?` is
false for it, and `rec/check`, `rec/recheck`, `rec/check-all`, `rec/recheck-all` and `rec/seal`
throw for it and run no check. [redefinition.md](redefinition.md) states the rules.

## What leaves no memory

- `rec/probe` and `rec/probe-all` ask a type's checks about plain maps. They make no draft and
  remember nothing. Given a draft or a value as the map to ask about, a probe reads the entries
  and neither reads nor writes the memory.
- `rec/clean` returns a draft that remembers what the draft it was given remembers.

## Not promised

- That a remembered check would pass now. Code that must know calls `rec/recheck`.
- Anything about how the memory is held. Code reads it through `rec/proves?`,
  `rec/proven-checks` and `rec/proven-concerns` only, and nothing but a run of the type's own
  checks writes it: [guarantee.md](../guarantee.md) states what tests check of this.
