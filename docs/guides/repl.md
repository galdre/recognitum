# Working at a REPL: when a type is defined again

The task: during development, the form that defines a type is evaluated again, by hand or by a
tool that reloads namespaces. Afterward the values made before throw on a write and on a call
of `rec/check`, and a function that asks `rec/sealed?` of them now refuses them. The work is to
bring what the session holds up to the new definition.

The rule behind all of it: evaluating a `rec/defproven` or `rec/defproven-in` form again makes
a new class under the same name. That is a **redefinition** of the type. The new definition is
the type's **current definition**, and the earlier one is a **displaced definition**. A value
made before belongs to the earlier definition, keeps its entries, and proves nothing, because
the checks of the current definition never ran on it.
[reference/redefinition.md](../reference/redefinition.md) states every case; this guide shows
what to do.

## The solution

A session defines a type and holds some values of it:

```clojure
(ns workbench.card
  (:require [recognitum.core :as rec]))

(rec/defproven Card [suit rank]
  rec/checks
  (suit [] "the suit is one of four" (contains? #{:clubs :diamonds :hearts :spades} suit))
  (rank [] "the rank is from 1 to 13" (and (int? rank) (<= 1 rank 13))))

(def ace (map->Card {::suit :spades ::rank 1}))
(def hand (atom [(map->Card {::suit :hearts ::rank 12}) (map->Card {::suit :clubs ::rank 7})]))
(def make map->Card)
(def started (assoc (rec/draft Card) ::suit :hearts))
```

The form is then evaluated again, with a new rule: a hand holds no face cards.

```clojure
(rec/defproven Card [suit rank]
  rec/checks
  (suit [] "the suit is one of four" (contains? #{:clubs :diamonds :hearts :spades} suit))
  (rank [] "the rank is from 1 to 10" (and (int? rank) (<= 1 rank 10))))
```

What the session holds now belongs to the earlier definition:

```clojure
(rec/sealed? ace)
;; => false
(::rank ace)
;; => 1
(assoc ace ::rank 2)
;; ExceptionInfo: workbench.card/Card was redefined: this value is of an earlier definition, so it
;;   is not sealed and refuses writes and its type's methods. To prove it under the current
;;   definition: (rec/seal (rec/draft v))
(try (rec/check ace rec/every)
     (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))
;; => :recognitum/displaced
```

`rec/check`, `rec/recheck`, `rec/check-all`, `rec/recheck-all` and `rec/seal` throw for such a
value as the write does, with the same message, and run no check. So `rec/check` never
answers `true` for a value of an earlier definition.

One value is brought up to the current definition by opening it as a draft and sealing the
draft. A **draft** is an unchecked map of a type, and `rec/draft` of such a value makes a draft
of the current definition that holds the value's entries:

```clojure
(def ace (rec/seal (rec/draft ace)))

(rec/sealed? ace)
;; => true
```

A collection of values is brought up with one call. `(rec/drafting-all data f)` opens each
value that it reaches in the plain data `data` as a draft, calls `f` on the result, and seals
every draft. With `identity` as `f`, it changes nothing and seals. The checks that run are
those of the current definition, so a value that breaks the new rule fails, and the data of the
throw names it by its path:

```clojure
(keys (:failures (try (rec/drafting-all @hand identity)
                      (catch clojure.lang.ExceptionInfo e (ex-data e)))))
;; => ([0])

(swap! hand #(rec/drafting-all % (fn [drafts] (assoc-in drafts [0 ::rank] 10))))

(mapv rec/sealed? @hand)
;; => [true true]
```

## What else the session holds

**A constructor that was taken from its var.** `make` above holds the function that
`map->Card` named before. It makes nothing now, and its message names the constructor to call.
Code that calls `map->Card` by name gets the current one.

```clojure
(make {::suit :spades ::rank 1})
;; ExceptionInfo: workbench.card/Card was redefined: this constructor is of an earlier definition
;;   and makes nothing. Call the current workbench.card/map->Card
```

The same holds for a map that `(rec/data-readers)` returned before: call `rec/data-readers`
again.

**A draft that was opened before.** `started` above is a draft of the earlier definition. It
still reads and accepts writes, and it proves nothing: `rec/seal` and `rec/check` of it throw.
Its entries go into a draft of the current definition with `into`:

```clojure
(rec/check started rec/shape)
;; ExceptionInfo: workbench.card/Card was redefined: this draft is of an earlier definition and
;;   seals nothing. Make a value of the current definition with workbench.card/map->Card, or seal
;;   a draft of the class workbench.card now names Card: (rec/seal (into (rec/draft Card) m))
(rec/check (into (rec/draft Card) started) ::suit)
;; => true
```

**A function that tests `instance?`.** A function that has already run `(instance? Card x)`
keeps the earlier class. After the redefinition its test is true of the earlier values, which
prove nothing, and false of the new ones. A function that must refuse a value without proof
asks `(rec/sealed? x)` as well as `(instance? Card x)`: `rec/sealed?` answers false for a value
of an earlier definition wherever it is asked. [sinks.md](sinks.md) shows such functions.

**A protocol that was extended to the class** with `extend-protocol` or `extend-type`. The
extension belongs to the earlier class. Evaluate the `extend-protocol` form again after the
type's form. A method that the type's own form lists needs nothing: it is defined with the
type. [methods.md](methods.md) shows both ways to give a type a method.

**A value of a `rec/defproven-in` type.** Such a type has no drafts. Its values are brought up
by making new ones from their entries, `(map->T (into {} v))`, and running the checks that the
code needs.

## Ways to hold less

- **Hold entries, not values, in a `def` that outlives a reload.** A plain map of the entries
  is not tied to a definition. Build the value from it where it is needed.
- **Put the `def` of a value in the same namespace as code that is reloaded with the type**, so
  that reloading the type also makes the value again.
- **Seal again on reload.** Where a running system keeps values in an atom across reloads, the
  function that runs after a reload can pass the atom's content through
  `(rec/drafting-all content identity)`, as above.

## A reload tool

A tool that removes a namespace and loads it again, as `clojure.tools.namespace` does, defines
each type of the namespace again. Everything above applies after each reload. A definition
that is evaluated after its name was unmapped with `ns-unmap` is a redefinition too.

## A form that fails

A definition that is refused, or whose check or method does not compile, defines nothing: the
earlier definition stays current, and its values stay sealed. So a typing mistake in a check
does not cost the session its values.

```clojure
(rec/defproven Card [suit rank]
  rec/checks
  (suit [no-such-check] "the suit is one of four" (keyword? suit)))
;; ExceptionInfo: workbench.card/Card, line 3: wait no-such-check of suit is not a check of Card. Its own checks: suit
(rec/sealed? ace)
;; => true
```

## What a redefinition is not

Evaluating again a function that a check body calls does not define the type again. The values
stay sealed, though the function may now answer differently for them. `rec/recheck` runs the
checks with the function as it is now, and answers `true` or a report.
[guarantee.md](../guarantee.md) states this limit.
