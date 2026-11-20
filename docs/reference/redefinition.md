# Redefinition

Evaluating a `rec/defproven` or `rec/defproven-in` form again defines a new class under the same
name. The new definition is the type's **current definition**, and the earlier one is a
**displaced definition**. A value of a displaced definition keeps its entries and proves
nothing: `rec/sealed?` and `rec/proves?` answer false for it. A write that changes it throws,
and so does each call that would seal it or run checks on it: `rec/seal`, `rec/check`,
`rec/recheck`, `rec/check-all` and `rec/recheck-all`. None of these calls runs a check of the
displaced definition.

This matters at a REPL and under any tool that reloads code. A reload that removes the
namespace first and loads it again, as `clojure.tools.namespace` does, is a redefinition too,
and so is a definition made after the name was unmapped with `ns-unmap`. A definition that
is refused, or whose check or method does not compile, displaces nothing: the earlier
definition stays current.

```clojure
(ns mint.coin
  (:require [recognitum.core :as rec]))

(defprotocol Describe
  (describe [coin]))

(defprotocol Weigh
  (grams [coin]))

(rec/defproven Coin [face ^:optional year]
  rec/checks
  (face [] "the face is a keyword" (keyword? face))
  (year [] "the year is a whole number" (int? year))

  Describe
  (describe [_] (str "a coin showing " (name face))))

(extend-protocol Weigh
  Coin
  (grams [_] 7))

(def old-coin (map->Coin {::face :heads}))
(def old-draft (assoc (rec/draft Coin) ::face :tails))
(def make map->Coin)
(def OldCoin Coin)
(defn coin? [x] (instance? Coin x))

(coin? old-coin)
;; => true
```

Now the form is evaluated again:

```clojure
(rec/defproven Coin [face ^:optional year]
  rec/checks
  (face [] "the face is a keyword" (keyword? face))
  (year [] "the year is a whole number" (int? year))

  Describe
  (describe [_] (str "a coin showing " (name face))))
```

## A value of a displaced definition

| Call, given the value | What it does |
|---|---|
| A read, `=`, `hash`, printing, `str` | As before the redefinition. |
| `rec/sealed?` | False. |
| `rec/proves?` | False, whatever it is given as a selection. It does not read the selection, so a keyword that names nothing does not make it throw. |
| `rec/proven-checks`, `rec/proven-concerns` | The empty set. |
| A write that changes the value | Throws an `ex-info` whose `:error` is `:recognitum/displaced`. |
| A method of a protocol or an interface that the definition lists, other than `toString` | Throws the same. |
| `rec/seal`, `rec/check`, `rec/recheck` | Throw the same, and run no check. |
| `rec/check-all`, `rec/recheck-all`, where the value is among those given | Throw the same, before any check of any value or draft given runs. |
| A method of a protocol that was extended to the class from outside the definition | Answers. |
| `rec/draft` | A draft of the current definition that holds the value's entries and remembers nothing. |
| `rec/drafting`, `rec/drafting-all` | Open the value as `rec/draft` does, and seal the result under the current definition. |
| `rec/seal-all`, where the value is in the shape | Fails, and lists the value at its path with the `:error` `:recognitum/displaced`. |
| `rec/probe`, given the current class and the value as the map to ask about | Reads the value's entries, as it reads any map. |

```clojure
(::face old-coin)
;; => :heads
(rec/sealed? old-coin)
;; => false
(assoc old-coin ::year 1999)
;; ExceptionInfo: mint.coin/Coin was redefined: this value is of an earlier definition, so it
;;   is not sealed and refuses writes and its type's methods. To prove it under the current
;;   definition: (rec/seal (rec/draft v))
(try (describe old-coin)
     (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))
;; => :recognitum/displaced
(try (rec/check old-coin rec/every)
     (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))
;; => :recognitum/displaced
(try (rec/check-all [(map->Coin {::face :tails}) old-coin] rec/every)
     (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))
;; => :recognitum/displaced
(rec/proves? old-coin rec/every)
;; => false
```

The message of each of these throws is the message of the write above. `rec/check`,
`rec/recheck`, `rec/check-all` and `rec/recheck-all` also throw for something that is no
selection, and for a keyword that names no check of the type: [selections.md](selections.md)
states those two throws. Where one of these calls is given both the value and such a
selection, which of the two throws comes is not promised.

A write that changes nothing does not throw, and returns the value, which is still not sealed.
`assoc` of the very object that a key holds, and `dissoc` of an absent key, change nothing. A
write of an object that is equal to the one a key holds, and is not that object, changes the
value, so it throws.

### Proving the value again

`(rec/seal (rec/draft v))` runs the checks of the current definition on the entries of `v`, and
returns a value of the current class or throws. Reading the value's printed form does the same,
since the tag reads through the current `map->Coin`.

```clojure
(rec/sealed? (rec/seal (rec/draft old-coin)))
;; => true
```

Where the type's name no longer names a definition of the type, `rec/draft` of the value throws
an `ex-info` whose `:error` is `:recognitum/no-current-definition`. That is the case after
`ns-unmap` of the name, and where the name now names a plain record.

### A value of a `rec/defproven-in` type

A value of a displaced definition of a `rec/defproven-in` type reads as before and proves
nothing. The calls that throw `:recognitum/displaced` for a value of a `rec/defproven` type
throw it for this value too: a write that changes the value, a method that the definition
lists, `rec/seal`, `rec/check`, `rec/recheck`, `rec/check-all` and `rec/recheck-all`. The type
has no drafts, so the message names the current `map->T`, and such a value is proved again by
making a new one: `(map->T (into {} v))`, then the checks that the code asks for.

## Things held from before the redefinition

A redefinition replaces what the type's names refer to: the class `Coin`, and the vars
`map->Coin` and `->Coin`. Code that looks the names up afterward gets the current definition.
Anything that was taken from the names beforehand still belongs to the displaced definition:

| Held | What it does |
|---|---|
| A constructor, as `(def make map->Coin)` holds it | Throws an `ex-info` whose `:error` is `:recognitum/displaced-constructor`. The message names the current constructor. |
| An entry of a map that `(rec/data-readers)` returned | Throws the same. Call `rec/data-readers` again. |
| A draft: an unchecked map of the type, made with `rec/draft` | Reads and accepts writes as before, and proves nothing. `rec/proves?` is false, whatever selection it is given and whatever the draft remembered. `rec/seal`, `rec/check`, `rec/recheck`, `rec/check-all` and `rec/recheck-all` throw `:recognitum/displaced-constructor` and run no check; a batch that holds the draft throws before any check of any value or draft given runs. `rec/seal-all` fails, and lists the draft at its path with that `:error`. |
| The class, as `(def OldCoin Coin)` holds it | `(instance? OldCoin x)` is true of the displaced definition's values and false of the current one's. `rec/probe` given it throws `:recognitum/displaced-constructor`. `(rec/draft OldCoin)` makes a draft of the displaced definition, which the row above describes. |

```clojure
(make {::face :heads})
;; ExceptionInfo: mint.coin/Coin was redefined: this constructor is of an earlier definition
;;   and makes nothing. Call the current mint.coin/map->Coin
(rec/seal old-draft)
;; ExceptionInfo: mint.coin/Coin was redefined: this draft is of an earlier definition and
;;   seals nothing. Make a value of the current definition with mint.coin/map->Coin, or seal a
;;   draft of the class mint.coin now names Coin: (rec/seal (into (rec/draft Coin) m))
(try (rec/check old-draft rec/every)
     (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))
;; => :recognitum/displaced-constructor
(rec/proves? old-draft rec/every)
;; => false
(rec/sealed? (rec/seal (into (rec/draft Coin) old-draft)))
;; => true
```

`rec/check` of the draft throws with the message of its seal. The entries of the draft go into
a draft of the current definition with `into`, as the last call shows.

## `instance?` and `rec/sealed?`

For a `rec/defproven` type `T`, `(instance? T x)` and `(rec/sealed? x)` agree until `T` is
redefined. Afterward they can disagree, because code may still name the class of the displaced
definition:

- A function that ran `(instance? Coin x)` before the redefinition keeps the class it found
  then. Afterward its test is true of the displaced definition's values, which are not sealed,
  and false of the current definition's values.
- A function that first runs the test after the redefinition finds the current class, even
  where the function was compiled before the redefinition.
- A class held as a value, as `OldCoin` above, stays the class of the displaced definition.

`rec/sealed?` answers false for a value of a displaced definition wherever it is asked. Above,
`coin?` ran once before the redefinition:

```clojure
(def new-coin (map->Coin {::face :heads}))

[(coin? old-coin) (rec/sealed? old-coin)]
;; => [true false]
[(coin? new-coin) (rec/sealed? new-coin)]
;; => [false true]
[(instance? Coin old-coin) (instance? Coin new-coin)]
;; => [false true]
```

So a function that must refuse an unproven value, and that may run across a redefinition, asks
`(rec/sealed? x)` as well as `(instance? T x)`.

## A protocol extended from outside the definition

A method that the definition itself lists is guarded: called with a value of a displaced
definition, it throws. A protocol that was extended to the class with `extend-protocol` or
`extend-type` is not guarded, and the extension belongs to the class it was made for. So after
a redefinition, the displaced values still answer the method, and the values of the current
definition do not, until the protocol is extended to the new class.

```clojure
(grams old-coin)
;; => 7
(grams new-coin)
;; IllegalArgumentException: No implementation of method: :grams of protocol: #'mint.coin/Weigh found for class: mint.coin.Coin
```

## Not promised

- While a definition form is being evaluated, the earlier definition may already be displaced
  before the new names are in place. Code on another thread that makes values of the type
  during a redefinition may see either.
