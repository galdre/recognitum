# Values that are checked in parts

The task: a value is filled in over several steps, it is used between the steps, and different
code asks different checks of it. A potion is brewed, then bottled, then sold in a shop, and
may be sent to court. The shop needs the label and the price to be right. The court needs a
taster. Neither needs what the other needs, and a potion that is fit for one may be unfit for
the other.

The tool is `rec/defproven-in`. It defines a type from the same form as `rec/defproven`, with
one difference: nothing runs the type's checks but a call that asks to. The constructors and
the writes check nothing. A value remembers the checks that have passed on its entries. Code
that needs proof asks two questions of a value: `instance?` for the type, and
`(rec/proves? v sel)` for the checks it needs.

## The solution

Two **concerns** mark the checks. A concern is a mark that `rec/defconcern` defines, and a
check carries it where the concern's id, such as `::shop`, or its name, `shop`, follows the
clause's wait vector. A **context** is a
var that `rec/defcontext` defines to hold a **selection**, which is a value that selects some
of a type's checks. `guild-licensed` is a **source**, a function that a check body reads with
`rec/fetch-each`.

```clojure
(ns apothecary.potion
  (:require [clojure.string :as str]
            [recognitum.core :as rec]))

(defn non-blank? [s] (and (string? s) (not (str/blank? s))))

(defn recipe? [x]
  (and (map? x) (seq x) (every? non-blank? (keys x)) (every? pos-int? (vals x))))

(def the-queen-cannot-abide #{"garlic" "mandrake root"})

(defn guild-licensed
  "A source: for each herb, whether the apothecaries' guild licenses it for sale."
  [herbs]
  (zipmap herbs (map #(not= "nightshade" %) herbs)))

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
    (every? true? (vals (rec/fetch-each guild-licensed (keys recipe)))))

  (tasted [] ::court
    "a taster drank it first"
    (rec/extant? taster))
  (fit-for-the-queen [] ::court
    "it holds nothing the queen cannot abide"
    (not-any? the-queen-cannot-abide (keys recipe))))

(rec/defcontext on-the-shelf
  "Sold in the shop: every check but the court's."
  (rec/except rec/every court))

(rec/defcontext at-court
  "Served to the queen: every check but the shop's."
  (rec/except rec/every shop))
```

Each context asks for the shape check of every field, and for the checks of its own concern
and not of the other. The potion is then made, filled in, and sealed for one place at a time:

```clojure
(def brewed (map->Potion {::name "Draught of Courage"
                          ::recipe {"dragon pepper" 2 "garlic" 1 "honey" 3}}))

(def bottled (assoc brewed
                    ::label "Draught of Courage: dragon pepper, garlic, honey"
                    ::price 12))

(identical? bottled (rec/seal bottled on-the-shelf))
;; => true
(rec/proves? bottled on-the-shelf)
;; => true
(rec/proves? bottled at-court)
;; => false
(rec/seal bottled at-court)
;; ExceptionInfo: apothecary.potion/Potion failed 2 checks
;;   :apothecary.potion/fit-for-the-queen (it holds nothing the queen cannot abide): false
;;   :apothecary.potion/tasted (a taster drank it first): false
```

## Making and writing check nothing

A value of a `rec/defproven-in` type starts with no check passed. `rec/check` runs the checks
that a selection selects, and the value remembers each check that passed:

```clojure
(def fresh (map->Potion {::name "Tonic" ::recipe {"moonwort" 2}}))

(rec/proves? fresh rec/shape)
;; => false
(rec/check fresh rec/shape)
;; => true
(rec/proves? fresh rec/shape)
;; => true
```

- The constructor and the writes still refuse a key that is not the key of one of the type's
  fields.
- A value may lack a required field, since nothing checks it when it is made. `rec/proves?` is
  false, whatever the selection selects, while the value lacks one.
  [reference/absence-and-nil.md](../reference/absence-and-nil.md) shows this.
- The memory is written in place: `rec/check` changed what `fresh` remembers, and every holder
  of `fresh` sees it. [reference/memory.md](../reference/memory.md) states the rules.

## A write forgets only the checks that read what it changed

A write returns a new value. The new value remembers what the old one remembered, less each
check that reads a key the write changes. The recipe's shape check, `labelled` and `licensed`
read the recipe, so a potion with a new recipe has to pass those again for the shop, and the
old potion is as it was:

```clojure
(def mended (assoc bottled ::recipe {"dragon pepper" 2 "moonwort" 1 "honey" 3}))

(rec/proves? mended on-the-shelf)
;; => false
(rec/proven-checks mended)
;; => #{::name ::label ::price ::taster ::priced}
(rec/proves? bottled on-the-shelf)
;; => true
```

`::taster` is among the checks that `mended` remembers, though no taster is named: the shape
check of an optional field passes where the field is absent.

## Sealing against a context

`(rec/seal v sel)` asks for three groups of checks: the checks that `sel` selects, the checks
that those wait on, and the shape check of each field that `v` holds or is required to hold.
It runs those of them that `v` has not passed. It returns `v` itself, or throws as a
constructor of a `rec/defproven` type throws. After it
returns, `(rec/proves? v sel)` is true.

```clojure
(def served (assoc mended ::taster "Sir Gulp"))

(identical? served (rec/seal served at-court))
;; => true
(rec/proves? served on-the-shelf)
;; => false
(rec/check served on-the-shelf)
;; => {:failed {::labelled {:data false :blocked #{} :doc "the label names every herb"}}
;;     :blocked #{}}

(def relabelled (assoc served ::label "Draught of Courage: dragon pepper, moonwort, honey"))

(identical? relabelled (rec/seal relabelled on-the-shelf))
;; => true
(rec/proves? relabelled at-court)
;; => true
```

The write of the label made `relabelled` forget only the checks that read the label. So it
still passes the court's checks, and it is now proven for both places.

- `(rec/seal v)`, with no selection, seals against `rec/every`.
- `rec/check` answers `true` or a report and never throws for a failed check. `rec/seal`
  returns the value or throws. A function that goes on to act uses `rec/seal`, or asks
  `rec/proves?`: `true` from `rec/check` is not proof, as the section "A selection that selects
  nothing in a type" shows.
- `(rec/check-all potions on-the-shelf)` checks many potions in one pass, so that their reads of
  the guild go out in one call. `(rec/seal-all data sel)` seals each such value that it finds
  in the plain data `data`. [sources.md](sources.md) shows a batch.
- A context means nothing beyond its selection. `(rec/proves? v (rec/except rec/every court))`
  asks what `(rec/proves? v on-the-shelf)` asks. The context gives the selection a name and a
  docstring, and one place to change it.

## Why not a draft

A **draft** is an unchecked map of a `rec/defproven` type, and it is also filled in over steps.
The two differ in what the finished thing proves:

| | A draft of a `rec/defproven` type | A value of a `rec/defproven-in` type |
|---|---|---|
| Is checked | When a call asks, and wholly at its seal | Only when a call asks |
| A seal proves | Every check: `(rec/seal d sel)` throws unless `sel` is `rec/every` | The checks of the selection that the seal was given |
| The result of a seal | A new value, which is sealed: `rec/sealed?` is true | The same value, which is never sealed: `rec/sealed?` is false |
| Is an instance of the type's class | No | Yes, whatever it has passed |
| The question that asks for proof | `rec/sealed?` of the sealed value | `(rec/proves? v sel)` |

So `rec/defproven` with drafts fits a value that must pass every check before any code uses it.
`rec/defproven-in` fits a value that is used while only some checks have passed, by code that
says which checks it needs. A `rec/defproven-in` type has no drafts: `rec/draft`, `rec/clean`
and `rec/drafting` throw for it.

The cost of `rec/defproven-in` is that holding a value proves nothing. `(instance? Potion x)`
is true of a potion that has passed no check, so each function that needs proof must also ask
`rec/proves?`. [sinks.md](sinks.md) shows both questions, and [guarantee.md](../guarantee.md)
states what `rec/proves?` proves.

## A selection that selects nothing in a type

A seal by a selection that selects nothing in the value's type would prove nothing, so it is
refused. `Label` below has no check that carries `shop`:

```clojure
(rec/defproven-in Label [text]
  rec/checks
  (text [] "the text is written" (non-blank? text)))

(def label (map->Label {::text "Courage"}))

(rec/selects-nothing? shop Label)
;; => true
(rec/seal label shop)
;; ExceptionInfo: apothecary.potion/Label has no check that carries :apothecary.potion/shop, so a seal by it would prove nothing. If a check of Label should carry it, give that check its flag after its waits. If Label has nothing to prove for it, give Label a check that carries it and passes, as in (nothing-to-prove [] :apothecary.potion/shop "Why Label has nothing to prove." true)
(rec/proves? label shop)
;; => false
(rec/check label shop)
;; => true
```

The last line is why `true` from `rec/check` is not proof: by a selection that selects nothing,
`rec/check` runs nothing and answers `true`.

The refusal exists for one mistake: a check that was meant to carry a concern, and whose clause
does not name the concern. A type that has nothing to prove for a concern says so with a check
that carries the concern and passes:

```clojure
(rec/defproven-in Ribbon [color]
  rec/checks
  (color [] "the color is named" (non-blank? color))
  (sold-as-it-is [] ::shop "the shop asks nothing of a ribbon" true))

(def ribbon (map->Ribbon {::color "red"}))

(identical? ribbon (rec/seal ribbon shop))
;; => true
```

The refusal catches the mistake only where no other check of the type carries the concern.
Where another check does, the selection selects that check, and the seal runs it and does not
run the check whose clause does not name the concern.
[reference/selections.md](../reference/selections.md) states what each call does with a
selection that selects nothing.

## A longer example

In a checkout of the repository, `clojure -M:dev -m demo.potion-run` runs a longer version of
this example and prints each step. Its source is `dev/demo/potion.clj`.
