# Selections

A **selection** is a value that selects some of a type's checks. These functions take one:
`rec/check`, `rec/recheck`, `rec/check-all`, `rec/recheck-all`, `rec/seal`, `rec/seal-all`,
`rec/proves?`, `rec/probe`, `rec/probe-all`, `rec/checks-of` and `rec/selects-nothing?`. A
selection belongs to no type: the same selection selects different checks in different types,
and may select none.

## What each selection selects

| Selection | Selects, in a type |
|---|---|
| A type's own check id, such as `::fee-is-fair` | That check. |
| A concern, or the concern's id | The checks that carry the concern. |
| A bundle | The bundle's checks, where the type binds the bundle. |
| A check of a bundle, or that check's id | That check, where the type binds the bundle. |
| `rec/every` | Every check. |
| `rec/shape` | Every shape check: each check named after a field. |
| `rec/pure` | Every check that reads no source. |
| `(rec/fetching source)` | The checks that read `source`. |
| `(rec/reading k)` | The checks that read the field whose key is `k`, directly or through an input of a bundle. |
| `(rec/union s ...)` | What any of its arguments selects. `(rec/union)` selects nothing. |
| `(rec/except s x ...)` | What `s` selects, less what each later argument selects. |
| A context: a var that `rec/defcontext` defined | What the selection it holds selects. |

A **concern** is a mark that `rec/defconcern` defines and that a check carries as a flag. A
**bundle** is a group of checks over named inputs that `rec/defchecks` defines and a type binds.
A **source** is a function that check bodies read with `rec/fetch`.

```clojure
(ns clinic.visit
  (:require [recognitum.core :as rec]))

(rec/defconcern billing "What the billing office asks of a visit.")
(rec/defconcern research "What a study asks of a visit.")

(rec/defchecks named [who]
  rec/checks
  (not-blank [] "the name is not blank" (and (string? who) (pos? (count who)))))

(rec/defproven Visit [patient doctor ^:optional fee]
  named
  (who [] patient)

  rec/checks
  (patient [] (string? patient))
  (doctor  [] (string? doctor))
  (fee     [] (nat-int? fee))
  (fee-is-fair [] billing "the fee is at most 500" (rec/when-extant fee (<= fee 500)))
  (seen-by-another [clinic.visit/not-blank] "the doctor is not the patient" (not= patient doctor)))

(rec/checks-of ::fee-is-fair Visit)
;; => #{::fee-is-fair}
(rec/checks-of billing Visit)
;; => #{::fee-is-fair}
(rec/checks-of named Visit)
;; => #{::not-blank}
(rec/checks-of rec/shape Visit)
;; => #{::patient ::doctor ::fee}
(rec/checks-of (rec/reading ::patient) Visit)
;; => #{::patient ::not-blank ::seen-by-another}
(rec/checks-of (rec/except rec/every rec/shape billing) Visit)
;; => #{::not-blank ::seen-by-another}
```

`(rec/checks-of sel x)` returns the ids of the checks that `sel` selects in the type of `x`,
which is a value, a draft or a type's class.

## What a keyword means

A keyword names a concern or a bundle's check where `rec/defconcern` or `rec/defchecks` defined
a var of the keyword's name in the keyword's namespace. Here `::billing` is the id of the
concern `billing`, and `::not-blank` is the id of the bundle's check `not-blank`. Any other
keyword is a type's own check id. So the concern and its id select the same checks:

```clojure
(= (rec/checks-of billing Visit) (rec/checks-of ::billing Visit))
;; => true
```

From another namespace, the id is written in full, `:clinic.visit/billing`, or the concern is
named through its var, `visit/billing`.

## A keyword that names nothing

- `rec/union` and `rec/except` throw when they are called with a keyword that names no concern,
  no bundle's check, and no check of any type that the keyword's namespace defines.
- A keyword that is some type's own check id is refused later, when the selection meets a type
  that lacks the check. `rec/check`, `rec/recheck`, `rec/check-all`, `rec/recheck-all`,
  `rec/proves?`, `rec/probe`, `rec/probe-all`, `rec/checks-of` and `rec/selects-nothing?` throw.
  So does `rec/seal` given a sealed value (a value of a `rec/defproven` type), or a value of a `rec/defproven-in` type, whose type
  lacks the check, and so does `rec/seal-all` given such a value of a `rec/defproven-in` type.

Both throws are `ex-info` whose data holds `:error` `:recognitum/unknown-name`.

```clojure
(rec/union ::no-such-check)
;; ExceptionInfo: no concern, bundle check or check of a type is named :clinic.visit/no-such-check

(rec/defproven Note [text]
  rec/checks
  (text [] (string? text)))

(rec/checks-of ::fee-is-fair Note)
;; ExceptionInfo: clinic.visit/Note has no check :clinic.visit/fee-is-fair, and no concern or bundle check is named :clinic.visit/fee-is-fair
```

## A selection that selects nothing in a type

A selection that names a concern or a bundle is not refused in a type that has no check for
it. It selects nothing there: `research` selects nothing in `Visit`, since no check of `Visit`
carries it. `(rec/selects-nothing? sel x)` answers whether `sel` selects nothing in the type of
`x`: none of its checks, and the presence of none of its required fields. (The presence of a
required field is itself a check, with no name.)

The table below names three kinds of thing that a call may be given. A **sealed value** is a
value of a `rec/defproven` type, and passes every check. A **draft** is an unchecked map of such
a type. A value of a `rec/defproven-in` type is checked only when a call asks, and remembers
the checks that passed on it.

What a call does with a selection that selects nothing depends on the call, and on what the
call is given:

| Call | Given a selection that selects nothing in the type |
|---|---|
| `rec/check`, `rec/recheck`, `rec/check-all`, `rec/recheck-all`, `rec/probe`, `rec/probe-all` | Runs nothing and answers `true`. A probe of a map that holds a key the type does not declare answers a report instead, with that key under `:undeclared`. |
| `(rec/seal v sel)` of a value of a `rec/defproven-in` type | Throws, before any check runs, an `ex-info` whose `:error` is `:recognitum/selects-nothing`: the seal would prove nothing. |
| `(rec/seal-all shape sel)` | Fails, and lists each such value of a `rec/defproven-in` type at its path, with that `:error`. |
| `(rec/proves? v sel)` of a value of a `rec/defproven-in` type | False, whatever the value has passed. |

`rec/every` is the exception: a seal by `rec/every`, or with no selection, is never refused for
selecting nothing, even in a type with no check. A sealed value is not refused either:
`(rec/proves? v sel)` is true of a sealed value `v` by a selection that selects nothing in its
type, and `(rec/seal v sel)` returns `v`.

```clojure
(rec/selects-nothing? research Visit)
;; => true
(rec/check (rec/draft Visit) research)
;; => true

(rec/defproven-in Referral [patient]
  rec/checks
  (patient [] (string? patient)))

(def referral (map->Referral {::patient "Ada"}))

(try (rec/seal referral research)
     (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))
;; => :recognitum/selects-nothing
(rec/proves? referral research)
;; => false
(identical? referral (rec/seal referral))
;; => true
```

So `true` from `rec/check` by a selection does not show that any check ran. Code that needs
proof by a concern asks `rec/proves?`, and a `rec/defproven-in` type that has nothing to prove
for a concern says so with a check that carries the concern and passes, as the docstring of
`rec/seal` describes.

## What `rec/proves?` does with a selection

`(rec/proves? x sel)` reads `sel` before it answers, where `x` is a sealed value, a draft or a
value of a `rec/defproven-in` type:

- Where `sel` is or holds a keyword that names no check of the type of `x`, no concern and no
  bundle's check, `rec/proves?` throws an `ex-info` whose `:error` is
  `:recognitum/unknown-name`. The id of another type's own check is such a keyword.
- Where `sel` is not a selection, such as `42`, the `:error` is `:recognitum/not-a-selection`.

`(rec/seal v sel)` of a sealed value `v` reads `sel` in the same way: it throws the same two
errors, and otherwise returns `v`.

Where `rec/proves?` does not throw, its answer depends on what `x` is:

| `x` | `(rec/proves? x sel)` |
|---|---|
| A sealed value | True for every selection. |
| A draft | False while the draft lacks a required field, and while it holds a key that its type does not declare. Otherwise, whether the draft remembers as passing the checks that `sel` selects, the checks that those wait on, and the shape check of each field that it holds. |
| A value of a `rec/defproven-in` type | False while the value lacks a required field, and where `sel` is not `rec/every` and selects nothing in the type. Otherwise, whether the value remembers those same checks as passing. |
| A value or a draft of a displaced definition, which is a definition of a type that a later definition replaced | False. `sel` is not read, so nothing throws. |
| A type's class, a plain map, or anything else | False. `sel` is not read, so nothing throws. |

[memory.md](memory.md) states what a draft and a value of a `rec/defproven-in` type remember.

```clojure
(def visit (map->Visit {::patient "Ada" ::doctor "Grace"}))

(rec/proves? visit billing)
;; => true
(rec/proves? visit research)
;; => true
(rec/proves? visit ::text)
;; ExceptionInfo: clinic.visit/Visit has no check :clinic.visit/text, and no concern or bundle check is named :clinic.visit/text
(rec/proves? visit 42)
;; ExceptionInfo: not a selection: 42
(rec/proves? {::patient "Ada" ::doctor "Grace"} ::text)
;; => false
```

### `rec/proves?` does not ask which type a value has

A selection belongs to no type, so a true answer from `(rec/proves? x sel)` says that `x`
proves `sel` in the type of `x`, whatever type that is. It does not say that `x` is an instance of the type:
a draft that remembers the checks answers true. Above, `visit` proves `research`, which no
check of `Visit` carries. In the same way, a sealed value of any type proves `billing`:

```clojure
(rec/proves? (map->Note {::text "rest"}) billing)
;; => true
(rec/proves? (rec/draft visit) billing)
;; => true
```

So a function that needs an instance of one type asks `(instance? T x)` as well as
`(rec/proves? x sel)`. [guides/sinks.md](../guides/sinks.md) shows such a function.

## A selected check runs the checks it waits on

A run by a selection runs each selected check and each check that a selected check waits on,
directly or through other checks. A check that a selected check waits on runs even where
`rec/except` removed it from the selection. Where such a check fails, the report explains under
`:pulled-back` which check waited on it. `rec/checks-of` lists only
the checks that the selection itself selects.

```clojure
(def visit-draft (into (rec/draft Visit) {::patient "" ::doctor "Grace"}))

(rec/checks-of (rec/except rec/every named) Visit)
;; => #{::patient ::doctor ::fee ::fee-is-fair ::seen-by-another}
(let [report (rec/check visit-draft (rec/except rec/every named))]
  [(keys (:failed report)) (keys (:pulled-back report))])
;; => [(::not-blank) (::not-blank)]
```

## Required fields

The presence of a required field is a check with no name. The docstring of `rec/check` states
which selections ask the presence of which fields; [absence-and-nil.md](absence-and-nil.md)
shows the effect.

## Contexts

`(rec/defcontext name doc sel)` defines a var that holds the selection `sel`. A context means
nothing beyond its selection: each function above answers for the context as it answers for
`sel`.

```clojure
(rec/defcontext at-the-desk
  "What the front desk asks of a visit: every check but the billing office's."
  (rec/except rec/every billing))

(rec/checks-of at-the-desk Visit)
;; => #{::patient ::doctor ::fee ::not-blank ::seen-by-another}
```

## A selection with `rec/seal`

A draft seals against every check. `(rec/seal d sel)` of a draft throws, running nothing,
unless `sel` is `rec/every`; the `:error` is `:recognitum/draft-selection`. Only a value of a
`rec/defproven-in` type is sealed against a selection. `(rec/seal v sel)` of a sealed value `v`
runs nothing, and returns `v` unless `sel` makes it throw, as the section on `rec/proves?`
states.

## Not promised

- That a selection selects anything in a given type. `rec/selects-nothing?` answers that.
