# Functions that refuse a value without proof

The task: a function has an effect that is right only where a value's checks have passed. It
records a sale, writes a row, or sends a payment. Such a function is called a **sink** in this
guide. The sink must refuse a value that lacks the proof it needs, and the code base must show
that every sink does.

Three things make a sink safe, and each has one place:

- The **proof** is in the value. The library answers whether the checks passed on exactly this
  value: `rec/sealed?` for a type that `rec/defproven` defined, and `(rec/proves? x sel)` for a
  type that `rec/defproven-in` defined. A plain map with the same entries proves nothing.
- The **gate** is in the sink. A gate is the test at the top of the function that refuses a
  value without proof. Only the code that receives a value can refuse it.
- The **coverage**, which is the assurance that every sink has its gate, is in a test. Neither
  a value nor a sink can see the rest of the code.

## The solution

A potion is checked in parts: the shop asks some checks of it and the court asks others.
`rec/defproven-in` defines such a type, whose values are made without checks and remember the
checks that have passed on them. A **concern** marks checks, and a **context** is a var that
holds a selection of checks. [checked-in-parts.md](checked-in-parts.md) explains each of these.

```clojure
(ns apothecary.counter
  (:require [clojure.string :as str]
            [recognitum.core :as rec]))

(rec/defconcern shop "What the shop needs before it sells a potion.")
(rec/defconcern court "What the court needs before the queen drinks a potion.")

(rec/defproven-in Potion [name ^:optional price ^:optional taster]
  rec/checks
  (name   [] "the potion has a name" (string? name))
  (price  [] "the price is a whole number of pennies" (pos-int? price))
  (taster [] "the taster is named" (string? taster))
  (priced [] ::shop "the potion has a price" (rec/extant? price))
  (tasted [] ::court "a taster drank it first" (rec/extant? taster)))

(rec/defcontext on-the-shelf
  "Sold in the shop: every check but the court's."
  (rec/except rec/every court))

(rec/defcontext at-court
  "Served to the queen: every check but the shop's."
  (rec/except rec/every shop))

(defn- gate
  "Throws unless `x` is a Potion that is proven against the context held by the var `context`."
  [x context sink]
  (when-not (and (instance? Potion x) (rec/proves? x @context))
    (throw (ex-info (str sink " takes only a potion proven " (:name (meta context)))
                    {:error ::not-proven :sink sink :context (symbol context)}))))

(def till (atom []))

(defn ring-up!
  "Records the sale of `potion` in the shop's till, and returns the receipt. Refuses a potion
  that is not proven `on-the-shelf`."
  [potion]
  (gate potion #'on-the-shelf 'ring-up!)
  (let [receipt {:sold (::name potion) :pennies (::price potion)}]
    (swap! till conj receipt)
    receipt))

(defn sell!
  "Sells `potion` over the counter. Refuses a potion that is not proven `on-the-shelf`."
  [potion]
  (gate potion #'on-the-shelf 'sell!)
  (ring-up! potion))

(defn serve-to-the-queen!
  "Serves `potion` to the queen. Refuses a potion that is not proven `at-court`."
  [potion]
  (gate potion #'at-court 'serve-to-the-queen!)
  (::name potion))
```

The sinks refuse a plain map, a potion that has passed nothing, and a potion that is proven
for the other place:

```clojure
(def entries {::name "Draught of Courage" ::price 12})

(def bottled (rec/seal (map->Potion entries) on-the-shelf))

(sell! entries)
;; ExceptionInfo: sell! takes only a potion proven on-the-shelf
(sell! (map->Potion entries))
;; ExceptionInfo: sell! takes only a potion proven on-the-shelf
(sell! bottled)
;; => {:sold "Draught of Courage" :pennies 12}
(serve-to-the-queen! bottled)
;; ExceptionInfo: serve-to-the-queen! takes only a potion proven at-court
```

## What the gate asks

The gate asks two questions, and needs both:

- **`(instance? Potion x)`: is this a potion?** `rec/proves?` does not ask which type a value
  has. `(rec/proves? x on-the-shelf)` is true where `x` is a sealed value of a `rec/defproven`
  type that has nothing to do with potions, and where `x` is a value of another
  `rec/defproven-in` type that has passed the checks that `on-the-shelf` selects in that type.
  A gate that asked `rec/proves?` alone would let such a value through, and the sink would
  then read fields that the value does not have.
  [reference/selections.md](../reference/selections.md) states what `rec/proves?` answers for
  each kind of thing it is given.
- **`(rec/proves? x @context)`: has this potion passed the checks that this sink needs?** The
  answer is about the value in hand. It is false for a plain map and for a potion that has
  passed nothing, and it is true or false of one potion for each context separately.

`rec/proves?` runs nothing: it reads what the value remembers. So the gate never runs a check,
and the code that calls the sink is the code that proves the potion. `(rec/seal v sel)` does
that for a value of a `rec/defproven-in` type: it runs the checks of `sel` that `v` has not
passed, and returns `v` or throws.

```clojure
(sell! (rec/seal (map->Potion entries) on-the-shelf))
;; => {:sold "Draught of Courage" :pennies 12}
(sell! (rec/seal (map->Potion {::name "Unpriced"}) on-the-shelf))
;; ExceptionInfo: apothecary.counter/Potion failed 1 check
;;   :apothecary.counter/priced (the potion has a price): false
```

## A sink for a type that `rec/defproven` defined

A sealed value of such a type has passed every check, so the gate asks `rec/sealed?` in the
place of `rec/proves?`, and still asks for the type:

```clojure
(rec/defproven Coin [pennies]
  rec/checks
  (pennies [] "a coin is worth a positive number of pennies" (pos-int? pennies)))

(defn bank!
  "Adds `coin` to the till. Refuses anything but a sealed Coin."
  [coin]
  (when-not (and (instance? Coin coin) (rec/sealed? coin))
    (throw (ex-info "bank! takes only a sealed Coin" {:error ::not-proven})))
  (swap! till conj {:banked (::pennies coin)}))

(bank! {::pennies 5})
;; ExceptionInfo: bank! takes only a sealed Coin
(bank! (rec/draft Coin))
;; ExceptionInfo: bank! takes only a sealed Coin
(bank! (rec/draft (map->Coin {::pennies 5})))
;; ExceptionInfo: bank! takes only a sealed Coin
```

The last call shows why this gate asks `rec/sealed?`. A draft that is opened from a sealed
coin remembers every check, so `(rec/proves? x rec/every)` is true of it, and a draft is not
a value of the type: the next write to it runs no check.

`(instance? Coin x)` alone is not the gate. While the type's form is evaluated only once,
`instance?` and `rec/sealed?` agree. After the form is evaluated again, a function that has
already run can still hold the earlier class, and its `instance?` is then true of values that
prove nothing. `rec/sealed?` is false for them wherever it is asked.
[repl.md](repl.md) and [reference/redefinition.md](../reference/redefinition.md) give the
details.

## Where the gate goes

`sell!` has its gate at the top, where a reader of the function looks first. `ring-up!`, which
does the write, has a gate of its own, so the write refuses an unproven potion even from a
caller that did not go through `sell!`. The two places are not exclusive. The second gate
runs no check: it reads what the value remembers.

A gate asks about the past. The proof says that each check passed when it last ran. Where a
check reads a source, such as a database, and the answer may have changed since, the sink
calls `rec/recheck` before it acts, and decides by the report. `rec/recheck` throws for a
value of an earlier definition of its type, so it answers `true` for no such value.
[sources.md](sources.md) shows a recheck, and [guarantee.md](../guarantee.md) states what the
proof covers.

## The test that every sink has its gate

The convention here is that every public function whose name ends in `!` is a sink. The test
finds them by that convention, hands each one several things that prove nothing, and expects
each to refuse all of them. A sink that is added later without a gate fails the test.

```clojure
(rec/defproven-in Ribbon [color]
  rec/checks
  (color [] "the color is named" (string? color)))

(defn sinks
  "The public functions of this namespace whose names end in `!`, by name."
  []
  (into (sorted-map)
        (for [[sym v] (ns-publics 'apothecary.counter)
              :when (and (str/ends-with? (name sym) "!") (fn? @v))]
          [sym @v])))

(defn refused?
  "Whether `sink` refuses `x` with the gate's error."
  [sink x]
  (= ::not-proven
     (try (sink x) nil
          (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))))

(def without-proof
  [entries                                             ; a plain map
   (map->Potion entries)                               ; a potion that has passed nothing
   (rec/seal (map->Ribbon {::color "red"}) rec/every)  ; a proven value of another type
   nil])

(into {} (for [[sym sink] (sinks)]
           [sym (every? #(refused? sink %) without-proof)]))
;; => {bank! true ring-up! true sell! true serve-to-the-queen! true}
```

In a test namespace, the last expression is the body of a test that expects `true` for every
sink. The test needs two more assertions, which the expression above does not make:

- **Assert the names of the sinks:** `(keys (sinks))`. A test that finds no sink passes for the
  wrong reason.
- **Hand each sink a value that it should accept, and assert that the sink does not refuse
  it.** Otherwise a gate that refuses everything would pass.

The repository's own example is `every-potion-sink-has-its-gate` in
`test/recognitum/demo_test.clj`, for the sinks of `dev/demo/potion.clj`.
