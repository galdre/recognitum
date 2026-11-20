# Checks that ask a database or a service

The task: a rule of a type cannot be judged from the value alone. Whether a clerk may refund an
order is a fact that a permission service holds, and whether a product exists is a fact that a
catalogue holds. The check must ask, and a batch of values must not make one query for each
value.

The tool is the **source**: a function that takes a vector of distinct keys and returns a map
from each key to its answer. A check body reads a key from a source with `rec/fetch`. The body
never calls the source: the library collects the reads of every check that one call of the
library runs, and calls the source with all of their keys.

## The solution

A refund is valid where the actor holds the grant to refund the order, and the amount is within
the actor's limit. Both facts are in a permission service, which two sources stand for here.
`calls` records each call of a source.

```clojure
(ns desk.refund
  (:require [recognitum.core :as rec]))

(def calls (atom []))

(def grants (atom #{["dana" :refund 41] ["dana" :refund 42] ["eli" :refund 42]}))

(defn allowed
  "A source: for each key `[user action order-id]`, whether the user holds that grant."
  [ks]
  (swap! calls conj [:allowed ks])
  (into {} (map (fn [k] [k (contains? @grants k)])) ks))

(defn refund-limit
  "A source: for each user, the largest refund in cents that the user may issue. A user with
  no limit on file is absent from the answer."
  [users]
  (swap! calls conj [:refund-limit users])
  (select-keys {"dana" 5000 "eli" 1000} users))

(rec/defproven Refund [actor order-id amount]
  rec/checks
  (actor    [] "the actor is named" (string? actor))
  (order-id [] "the order id is a positive whole number" (pos-int? order-id))
  (amount   [] "the amount is a positive whole number of cents" (pos-int? amount))

  (may-refund []
    "the actor holds the refund grant for the order"
    (true? (rec/fetch allowed [actor :refund order-id])))
  (within-limit [may-refund]
    "the amount is within the actor's refund limit"
    (<= amount (or (rec/fetch refund-limit actor) 0))))

(defn calls-by
  "The calls of the sources while `f` was called."
  [f]
  (reset! calls [])
  (f)
  @calls)
```

One refund makes one call of each source:

```clojure
(calls-by #(map->Refund {::actor "dana" ::order-id 42 ::amount 1500}))
;; => [[:allowed [["dana" :refund 42]]] [:refund-limit ["dana"]]]
```

Three refunds that are checked by one call also make one call of each source.
`rec/probe-all` asks the checks of a type about plain maps, and answers `true` or a report for
each:

```clojure
(def requests [{::actor "dana" ::order-id 42 ::amount 1500}
               {::actor "eli" ::order-id 42 ::amount 900}
               {::actor "eli" ::order-id 41 ::amount 900}])

(calls-by #(rec/probe-all Refund requests))
;; => [[:allowed [["dana" :refund 42] ["eli" :refund 42] ["eli" :refund 41]]]
;;     [:refund-limit ["dana" "eli"]]]
(mapv true? (rec/probe-all Refund requests))
;; => [true true false]
```

## Writing the source

- **A source takes a vector and returns a map.** The keys in the vector are distinct. A key may
  be any value: `allowed` takes vectors as its keys. A key that the source leaves out of its
  map reads as `nil`, which is why `within-limit` writes `(or ... 0)`.
- **Make one query for the whole vector.** Each call gives the source every key that the
  library has collected for it by then. Whether the source answers a call with one query is up
  to the source.
- **Keep the source in a var.** Two reads share a call only where both read the same
  function. A function that a var holds is the same function at every read. A function that
  is made anew at each read, as `(partial query db)` written in a check body would be, is a
  new source each time, and is called once for each read.

`(rec/fetch source k)` reads one key and returns its answer. `(rec/fetch-each source ks)` reads
every key of a collection and returns a map from each key to its answer, for a check that asks
about each member of a field:

```clojure
(defn listed
  "A source: for each sku, whether the catalogue lists it."
  [skus]
  (zipmap skus (map #(contains? #{"tea" "pot" "cup"} %) skus)))

(rec/defproven Basket [skus]
  rec/checks
  (skus [] "the skus are a vector of strings" (and (vector? skus) (every? string? skus)))
  (skus-listed [] "the catalogue lists every sku"
    (every? true? (vals (rec/fetch-each listed (distinct skus))))))

(rec/probe Basket {::skus ["tea" "urn"]})
;; => {:failed {::skus-listed {:data false :doc "the catalogue lists every sku" :blocked #{}}}
;;     :blocked #{}}
```

A read may not be written inside a function that the body builds, such as the function given to
`every?` or the body of a `for`: the definition is refused. `rec/fetch-each` is the way to read
for each member of a collection.
[reference/sources.md](../reference/sources.md) lists the places where a read is refused.

## Which reads share a call of a source

Reads share a call of a source where one call of the library runs their checks:

- A constructor, a write or `rec/seal` runs the checks of one value.
- `rec/check-all`, `rec/recheck-all` and `rec/probe-all` take many values, drafts or maps, and
  `rec/seal-all` takes plain data that holds many drafts. Each runs the checks of all of them
  in one pass.

So code that makes many values builds drafts and seals them with one `rec/seal-all`, or asks
first with `rec/probe-all`. A loop over `map->Refund` calls each source once for each value.
[reference/sources.md](../reference/sources.md) states how many calls a source receives.

## A read that waits for another check

`within-limit` names `may-refund` in its wait vector, so it runs only after `may-refund` has
passed. A refund whose actor has no grant is never asked about its limit: above,
`refund-limit` was called for two users, and eli's refund of order 41 added no key. Here the
only refund fails `may-refund`, and `refund-limit` is not called at all:

```clojure
(calls-by #(rec/probe Refund {::actor "eli" ::order-id 41 ::amount 900}))
;; => [[:allowed [["eli" :refund 41]]]]
```

For a batch, the library calls `allowed` first, with the keys of every refund in the batch. It
calls `refund-limit` afterward, with the keys of the refunds whose `may-refund` passed. So a
wait between two checks that read sources does not add a call for each value: here, each
source is still called once for the batch.

"Once" holds here because all the reads of each source are reached at one step of the run: each
`may-refund` reads `allowed` at the start, and each `within-limit` reads `refund-limit` after
its `may-refund` has passed. A source whose reads are reached at different steps is called more
than once for the batch. Two reads in one body are two steps, and so are a read in one check
and a read in a check that waits on it. However many values the batch holds, a source is called
no more times than the bound that
[reference/sources.md](../reference/sources.md#how-many-calls-a-source-receives) states.

## When the source's answer changes

A check that read a source judged the value by the answer that the source gave then. Nothing
runs the check again when the answer changes: the value stays sealed. Code that must know the
answer now calls `rec/recheck`, which runs the selected checks again and returns `true` or a
report. `(rec/fetching source)` selects the checks that read `source`:

```clojure
(def refund (map->Refund {::actor "dana" ::order-id 42 ::amount 1500}))

(swap! grants disj ["dana" :refund 42])

(rec/sealed? refund)
;; => true
(rec/check refund rec/every)
;; => true
(keys (:failed (rec/recheck refund (rec/fetching allowed))))
;; => (::may-refund)
(rec/sealed? refund)
;; => true
```

`rec/check` answered `true` without a call: a sealed value passes every check, so `rec/check`
runs nothing on it. The recheck reports the failure and leaves the value sealed. A function
that acts on the refund decides what to do with the report.
[reference/memory.md](../reference/memory.md) states what a value and a draft remember, and
[guarantee.md](../guarantee.md) states this limit of the proof.

## A source that fails

A source that throws an `Exception` fails each check whose read was in that call. The failure
data of each such check is `{:fetch-failed source :cause e}`, where `e` is what the source
threw:

```clojure
(defn stock
  "A source that cannot reach its database."
  [skus]
  (throw (java.io.IOException. "connection refused")))

(rec/defproven Pick [sku]
  rec/checks
  (sku [] (string? sku))
  (in-stock [] "the warehouse has the sku" (pos? (rec/fetch stock sku))))

(let [data (get-in (rec/probe Pick {::sku "tea"}) [:failed ::in-stock :data])]
  [(= stock (:fetch-failed data)) (ex-message (:cause data))])
;; => [true "connection refused"]
```

So the caller sees a source that throws as a failed check, with the cause in the report. A
constructor then throws its usual failure, and the cause is under `:failed` in the data of that
throw. The
library sets no timeout on a source and does not retry one: both belong in the source. The
docstring of `rec/fetch` states the other cases, among them an `Error` from a source, which
is not caught.

A body may catch the failure of its own read, to pass or to fail with data of its own. What
the body catches is an `ex-info` that the library made. Its data has one key,
`:recognitum.checks/fetch-failed`, which holds the source, and its cause is the exception that
the source threw. Its data has no `:error` key.

```clojure
(rec/defproven Reservation [sku]
  rec/checks
  (sku [] (string? sku))
  (in-stock [] "the warehouse has the sku, or cannot be asked"
    (try (pos? (rec/fetch stock sku))
         (catch clojure.lang.ExceptionInfo e
           (if (contains? (ex-data e) :recognitum.checks/fetch-failed)
             true
             (throw e))))))

(rec/sealed? (map->Reservation {::sku "tea"}))
;; => true
```

A body that catches a read of an absent field catches an `ex-info` of the same kind, whose data
has the one key `:recognitum.checks/absent`, which holds the field's key.

## Testing a type that reads a source

[testing.md](testing.md) shows how a test answers in a source's place.

## A longer example

In a checkout of the repository, `clojure -M:dev -m demo.authz` runs a longer version of the
refund example, and prints each step with the calls that the permission service received. Its
source is `dev/demo/authz.clj`.
