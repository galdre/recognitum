# Values built in steps, and values sealed together

The task: the data for a value arrives in pieces, or needs mending before it is valid, or
several values must all be made or none. A web form is one such case: the request holds
strings, some of them wrong, and the person who filled in the form should hear of every mistake
before anything is saved.

The tool is the **draft**: an unchecked map of a type that `rec/defproven` defined. A draft
accepts any write, remembers which checks have passed on its entries, and becomes a value when
`rec/seal` has run the checks that are left.

## The solution

A refund request comes in as a web request. The type's last check asks a **source**, a function
that check bodies read with `rec/fetch`; here the source stands for a permission service, and
`calls` records each call of it.

```clojure
(ns office.refund
  (:require [recognitum.core :as rec]))

(def calls (atom []))

(defn refund-limit
  "A source: for each user, the largest refund in cents that the user may issue."
  [users]
  (swap! calls conj users)
  (select-keys {"dana" 5000 "eli" 1000} users))

(rec/defproven Refund [actor order-id amount ^:optional note]
  rec/checks
  (actor    [] "the actor is named" (string? actor))
  (order-id [] "the order id is a positive whole number" (pos-int? order-id))
  (amount   [] "the amount is a positive whole number of cents" (pos-int? amount))
  (note     [] "the note is text" (string? note))
  (within-limit [] "the amount is within the actor's refund limit"
    (<= amount (or (rec/fetch refund-limit actor) 0))))

(defn request->draft
  "A draft of a Refund from a request: the actor from the session, the rest from the form's
  string parameters. A parameter that does not parse is held as given, so that its shape check
  fails on it."
  [{:keys [session params]}]
  (let [number (fn [s] (or (some-> s parse-long) s))]
    (cond-> (assoc (rec/draft Refund)
                   ::actor (:user session)
                   ::order-id (number (get params "order"))
                   ::amount (number (get params "amount")))
      (contains? params "note") (assoc ::note (get params "note")))))

(defn form-problems
  "What to tell the person who filled in the form: the docstring of each shape check that
  `draft` fails. Nil where every shape check passes."
  [draft]
  (let [answer (rec/check draft rec/shape)]
    (when-not (true? answer)
      (sort (map :doc (vals (:failed answer)))))))
```

The handler makes the draft, reports the form's mistakes without a call to the service, and
seals the draft once the form is mended:

```clojure
(def draft (request->draft {:session {:user "eli"} :params {"order" "42" "amount" "8oo"}}))

(form-problems draft)
;; => ("the amount is a positive whole number of cents")

(def mended (assoc draft ::amount 800))

(form-problems mended)
;; => nil
@calls
;; => []

(def refund (rec/seal mended))

(rec/sealed? refund)
;; => true
@calls
;; => [["eli"]]
```

A seal refuses a draft that holds a key that is not the key of one of the type's fields: it
throws before any check runs, and never drops the key. Code that means to drop such keys, as
for a form that sends more parameters than the type has fields, seals `(rec/clean d)`, which
is the draft `d` without them.

## What the solution relies on

**A draft accepts what a value refuses.** `(rec/draft Refund)` makes a draft that holds
nothing. A write to a draft runs no check, so the draft above could hold the string `"8oo"` as
its amount. A draft is not a value of the type: `rec/sealed?` is false for it, and it is not
an instance of the type's class.

**`rec/check` runs some of the checks and answers.** `(rec/check d sel)` runs the checks that
the **selection** `sel` selects and that `d` does not remember as passing, and the checks that
those wait on. It returns `true` or a report, and does not throw for a failed check.
`rec/shape` selects every shape check, which is each check named after a field. Two more
selections serve a form: `rec/pure` selects every check that reads no source, and `rec/every`
selects every check. [reference/selections.md](../reference/selections.md) lists the rest, and
[reference/failures.md](../reference/failures.md) states what a report holds.

**A draft remembers what passed.** After `form-problems` returned nil, `mended` remembered its
four shape checks, so the seal ran only `within-limit`, and the service was called once. A
write makes the new draft forget the checks that read a key the write changes, and no others.
[reference/memory.md](../reference/memory.md) states what a draft remembers and forgets.

**`rec/seal` returns a value or throws.** It runs every check that the draft does not remember
as passing. A seal that fails throws what the constructor throws, and leaves the draft
remembering the checks that passed:

```clojure
(def too-much (assoc mended ::amount 2500))

(rec/seal too-much)
;; ExceptionInfo: office.refund/Refund failed 1 check
;;   :office.refund/within-limit (the amount is within the actor's refund limit): false
(rec/proven-checks too-much)
;; => #{::actor ::order-id ::amount ::note}
```

**A key that is not a field's key stops the seal.** A draft accepts such a key, and no check
reads it, so `rec/check` can answer `true` for the draft. While the draft holds the key,
`rec/seal` throws for it and `rec/proves?` is false. `rec/clean` returns the draft without the
key, remembering the checks that passed:

```clojure
(def stray (assoc mended ::coupon "SPRING"))

(rec/seal stray)
;; ExceptionInfo: office.refund/Refund has no field :office.refund/coupon. Its fields: :office.refund/actor :office.refund/order-id :office.refund/amount :office.refund/note
(rec/check stray rec/every)
;; => true
(rec/proves? stray rec/every)
;; => false
(rec/proves? (rec/clean stray) rec/every)
;; => true
(rec/sealed? (rec/seal (rec/clean stray)))
;; => true
```

[reference/writes.md](../reference/writes.md) and
[reference/memory.md](../reference/memory.md) state the rules.

## Sealing many drafts together

An upload holds several refunds, and all of them must be issued or none. `rec/seal-all` takes
plain data that holds drafts (maps, vectors, lists and sets, nested as deep as needed) and
returns that data with each draft replaced by its value. A map, a vector, a set and a list each
come back as a collection of the same kind. Any other sequence, such as the lazy sequence that
`map` returns, comes back as a vector, and so does a queue. Where any draft fails,
`rec/seal-all` throws, and no draft is sealed.

`rec/seal-all` looks for drafts only in the collections that its docstring lists: Clojure's
maps, records, vectors, lists, sets, queues and sequences. It does not search anything else,
such as a Java `ArrayList`, an array, an atom or an object of a `deftype`. Such a holder comes
back as it is, and a draft inside it is still a draft that no check ran on. So seal a draft
before putting it in one of these, or give `rec/seal-all` the drafts in a vector.

```clojure
(defn draft-of [user amount]
  (request->draft {:session {:user user} :params {"order" "42" "amount" (str amount)}}))

(def upload {:approved [(draft-of "dana" 1500) (draft-of "eli" 900)]
             :held     (draft-of "eli" 2500)})

(reset! calls [])

(def failure
  (try (rec/seal-all upload)
       (catch clojure.lang.ExceptionInfo e (ex-data e))))

(:error failure)
;; => :recognitum/drafts-failed
(keys (:failures failure))
;; => ([:held])
(keys (:failed (get (:failures failure) [:held])))
;; => (::within-limit)
@calls
;; => [["dana" "eli"]]
```

The three drafts were checked by one call, so their reads of the service went out together:
`rec/seal-all` called `refund-limit` once, with the two distinct users of the three drafts.

The data of the throw holds two things to mend with:

- `:failures` maps the path of each draft that failed to the data that `rec/seal` would have
  thrown for that draft. A path is what `get-in` takes.
- `:drafts` is the data that was given, with every draft in place, each remembering the checks
  that passed on it. In `:drafts`, as in the data that a call returns, a sequence that is not a
  list has become a vector, so `assoc-in` follows a path into it. A list is still a list, which
  `assoc-in` cannot enter.

So the code mends the drafts at those paths and seals `:drafts` again. The second call runs
only the checks that the mending made the drafts forget:

```clojure
(reset! calls [])

(def issued
  (rec/seal-all (reduce-kv (fn [drafts path _] (assoc-in drafts (conj path ::amount) 1000))
                           (:drafts failure)
                           (:failures failure))))

(mapv rec/sealed? (conj (:approved issued) (:held issued)))
;; => [true true true]
@calls
;; => [["eli"]]
```

The docstring of `rec/seal-all` states which collections it looks into for drafts, what each
collection comes back as, what a path is for a set and for a map's key, and what it does with a
draft that holds drafts.

## A step that works on a value and on a draft

`(rec/drafting v f)` opens the sealed value `v` as a draft, calls `f` on the draft, and seals
what `f` returns. Given a draft, it calls `f` and returns the result unsealed. So a function
written with it works on its own, and also as one step among several that are sealed once:

```clojure
(defn with-note [refund text] (rec/drafting refund #(assoc % ::note text)))
(defn capped [refund cents] (rec/drafting refund #(update % ::amount min cents)))

(::note (with-note refund "damaged in transit"))
;; => "damaged in transit"
(rec/sealed? (with-note refund "damaged in transit"))
;; => true
```

`(rec/drafting-all data f)` opens each sealed value that it reaches in `data` as a draft,
calls `f` on the result, and seals what `f` returns as `rec/seal-all` does. Inside `f`, the two
steps above receive drafts, so they seal nothing, and the one seal at the end checks every
draft together:

```clojure
(reset! calls [])

(def audited
  (rec/drafting-all (:approved issued)
                    (fn [drafts] (mapv #(-> % (capped 700) (with-note "audited")) drafts))))

(mapv ::amount audited)
;; => [700 700]
(mapv rec/sealed? audited)
;; => [true true]
@calls
;; => [["dana" "eli"]]
```

## When a draft is the wrong tool

- **The data is complete and arrives at once.** `map->Refund` runs every check and names every
  failed check in one throw. A draft adds nothing.
- **The code must report every mistake in plain data, misspelled keys included, and build
  nothing.** That is `rec/probe`:
  [asking-without-building.md](asking-without-building.md).
- **Different code asks different checks of the value, and the value is used before every
  check has passed.** A draft seals against every check. A type that `rec/defproven-in` defines
  is checked in parts: [checked-in-parts.md](checked-in-parts.md).
- **A change of several keys is valid as a whole.** One `merge` or `into` on the value is one
  write, checked on its result: [reference/writes.md](../reference/writes.md).
