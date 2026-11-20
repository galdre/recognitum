# Sources and how they are called

A **source** is a function that takes a vector of distinct keys and returns a map from each key
to its answer. A check body reads one key from a source with `(rec/fetch source k)` and several
with `(rec/fetch-each source ks)`. A body never calls the source itself: the library collects
the reads that the checks of one call reach, and calls each source with the keys of all of
them. A key that the source leaves out of its map reads as `nil`.

```clojure
(ns pantry.recipe
  (:require [recognitum.core :as rec]))

(def calls (atom []))

(def shelf (atom {"flour" 500 "sugar" 200}))

(defn on-shelf
  "A source: the grams on the shelf of each ingredient."
  [ingredients]
  (swap! calls conj [:on-shelf ingredients])
  (select-keys @shelf ingredients))

(defn price-of
  "A source: the price of each ingredient."
  [ingredients]
  (swap! calls conj [:price-of ingredients])
  (select-keys {"flour" 2 "sugar" 3 "saffron" 90} ingredients))

(rec/defproven Recipe [ingredient grams]
  rec/checks
  (ingredient [] (string? ingredient))
  (grams      [] (pos-int? grams))
  (in-stock   [] "the shelf holds enough" (<= grams (or (rec/fetch on-shelf ingredient) 0)))
  (affordable [in-stock] "the ingredient costs under 10" (< (rec/fetch price-of ingredient) 10)))

(defn calls-by
  "The calls of the sources while `f` was called."
  [f]
  (reset! calls [])
  (f)
  @calls)
```

## How many calls a source receives

One call that runs checks is one **run**. A check may **wait** on other checks, which it names
in its wait vector: it runs only after they have passed. Within one run that does not throw:

- A source is asked for a key at most once, and each call of it passes distinct keys. Two
  checks, or two values, that read one key of one source share the answer.
- A source is asked for exactly the keys of the reads that running checks reach. A read in a
  branch that is not taken asks nothing, and neither does a read in a check that does not run.
- A source is called no more times than the longest chain of reads along any path of waits,
  each `rec/fetch` or `rec/fetch-each` being one link. Reads that do not depend on one
  another's answers go out in the same call.

How much one run covers depends on the call. In the table, a **draft** is an unchecked map of a
type, made with `rec/draft`:

| Call | The reads that share a source's calls |
|---|---|
| A constructor, a write, `rec/seal`, `rec/check`, `rec/recheck`, `rec/probe` | Those of the checks run on the one value, draft or map. |
| `rec/check-all`, `rec/recheck-all`, `rec/probe-all` | Those of every value, draft or map given. |
| `rec/seal-all` | Those of the drafts at one depth of nesting, counted from the innermost. Drafts that hold no draft are checked together first, then the drafts that hold them. |

Here four recipes are checked in one pass. `on-shelf` is called once, with three distinct keys.
`price-of` is called once, with the two distinct keys of the three recipes whose `in-stock`
passed:

```clojure
(defn draft-of [ingredient grams]
  (into (rec/draft Recipe) {::ingredient ingredient ::grams grams}))

(calls-by #(rec/check-all [(draft-of "flour" 100) (draft-of "sugar" 100)
                           (draft-of "flour" 250) (draft-of "saffron" 1)]
                          rec/every))
;; => [[:on-shelf ["flour" "sugar" "saffron"]]
;;     [:price-of ["flour" "sugar"]]]
```

Checked one at a time, the same four drafts make four runs, and each run calls `on-shelf`.

Sources are compared with `=`. So the reads of one source share its calls only where each read
names the same function, as a var does. A function that is made anew for each read is a new
source each time.

## How a read fails

The docstring of `rec/fetch` states each case. In short:

| What the source does | What follows |
|---|---|
| Throws an `Exception` | Every read of every key in that call fails its check, with the failure data `{:fetch-failed source :cause e}`. |
| Answers a key with a `Throwable` | The reads of that key fail their checks, with the same failure data. |
| Throws an `Error` | The `Error` propagates out of the call that ran the checks, and that call answers nothing for any value. |

A body may catch the failure of its own read, as it may catch any exception.

## Where a read may be written

`rec/fetch` and `rec/fetch-each` are legal only inside a check body, in call position. They
are refused in three places, when the definition expands:

- Inside a function that the body builds: `fn`, `#(...)`, `for`, `lazy-seq`, `delay`. Such a
  function would run the read outside the check. The body makes the read outside the function,
  and the function uses the answer.
- Inside `locking`. A read may wait for its source, and would hold the lock while it waits.
- In an input clause: the clause by which a type gives a value to an input of a bundle of
  checks that it binds.

`rec/extant?` and `rec/when-extant` are legal only in call position too, and they are refused
in none of the three places: they are accepted inside a function that the body builds, inside
`locking`, and in an input clause.

## Selecting by source

`(rec/fetching source)` selects the checks that read `source`, and `rec/pure` selects the checks
that read no source:

```clojure
(rec/checks-of (rec/fetching on-shelf) Recipe)
;; => #{::in-stock}
(rec/checks-of rec/pure Recipe)
;; => #{::ingredient ::grams}
```

## Answering in a source's place

Two ways give a check another answer than the source's:

- **The fourth argument of `rec/probe` and `rec/probe-all`**, which their docstrings name
  `overrides`, maps a source to a function of the same shape. The function is an **override**
  of the source: for that call only, every read of the source calls the function, and the source
  is not called. No other run, on this thread or another, sees the function, and nothing
  remembers the answer. Where the function fails, the failure data names the function, not the
  source, under `:fetch-failed`.
- **`with-redefs` on the source's var** replaces the source for every thread while it is in
  force, since a body reads a source through its var. A draft that is checked under it
  remembers the pass afterward: see [memory.md](memory.md). It suits a test in which no
  other thread reads the source.

```clojure
(calls-by #(rec/probe Recipe {::ingredient "saffron" ::grams 1}
                      rec/every
                      {on-shelf (fn [ingredients] (zipmap ingredients (repeat 1000)))}))
;; => [[:price-of ["saffron"]]]

(with-redefs [on-shelf (fn [ingredients] (zipmap ingredients (repeat 1000)))
              price-of (fn [ingredients] (zipmap ingredients (repeat 1)))]
  (rec/sealed? (map->Recipe {::ingredient "saffron" ::grams 1})))
;; => true
```

## Not promised

- The order in which two sources are called.
- For a run that throws: which keys it asked for and how many calls it made, beyond distinct
  keys that are each asked at most once.
- Anything about time. The library sets no timeout on a source and does not retry one.
