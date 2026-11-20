# How a write is checked

A **write** is a call of `assoc`, `dissoc`, `conj`, `merge` or `into` on a value or a draft, or
of a function built on them, such as `update`. What a write checks depends on what is written
to:

| The write is to | What the write does |
|---|---|
| A sealed value: a value of a `rec/defproven` type | Runs the checks that read a key the write changes. Returns a new sealed value, or throws. |
| A draft: an unchecked map of a type, made with `rec/draft` | Runs no check, and accepts any key. Returns a new draft, which forgets the checks that read a key the write changes. |
| A value of a `rec/defproven-in` type | Runs no check, and throws for a key the type does not declare. Returns a new value, which forgets the checks that read a key the write changes. |

The value or the draft that was written to is unchanged, as with any map.

```clojure
(ns bank.account
  (:require [recognitum.core :as rec]))

(rec/defproven Account [owner balance reserved ^:optional nickname]
  rec/checks
  (owner    [] "the owner is named" (string? owner))
  (balance  [] "the balance is a whole number" (nat-int? balance))
  (reserved [] "the reserved sum is a whole number" (nat-int? reserved))
  (nickname [] "the nickname is a string" (string? nickname))
  (reserved-is-covered [] "the balance covers the reserved sum" (<= reserved balance)))

(def account (map->Account {::owner "Ada" ::balance 100 ::reserved 80}))
```

## Which keys a write changes

A write changes a key where it gives the key an object that the key does not already hold, or
removes a key that is present. Two cases follow:

- A write of the very object that a key holds changes nothing, and neither does `dissoc` of an
  absent key. Such a write runs no check and forgets nothing.
- A write of an object that is equal to the one a key holds, and is not that object, changes
  the key.

A draft of a sealed value remembers every check as passing, and `rec/proven-checks` returns the
ids of the checks it remembers, so a draft shows which checks a write would run:

```clojure
(def draft (rec/draft account))

(defn forgotten-by
  "The ids of the checks that `written`, a draft made by a write to `draft`, forgot."
  [written]
  (reduce disj (rec/proven-checks draft) (rec/proven-checks written)))

(forgotten-by (assoc draft ::balance 90))
;; => #{::balance ::reserved-is-covered}
(forgotten-by (assoc draft ::owner (::owner draft)))
;; => #{}
(forgotten-by (assoc draft ::owner (String. "Ada")))
;; => #{::owner}
(forgotten-by (dissoc draft ::nickname))
;; => #{}
```

## Which writes of several keys are one write

A write is checked on its own result. So a change of two keys that is valid only as a whole
must be one write:

- `into`, `merge` of one map and `conj` of one map each write their keys together, as one write.
  The order of the keys does not matter.
- `assoc` of several keys is one write for each key, in the order given.
- `merge` or `conj` of several arguments is one write for each argument.
- A transient made from a sealed value makes one write, when `persistent!` is called.

```clojure
(::balance (merge account {::balance 50 ::reserved 30}))
;; => 50
(assoc account ::balance 50 ::reserved 30)
;; ExceptionInfo: bank.account/Account failed 1 check
;;   :bank.account/reserved-is-covered (the balance covers the reserved sum): false
(::balance (assoc account ::reserved 30 ::balance 50))
;; => 50
```

The second call throws because its first write, of the balance alone, leaves a balance of 50
under a reserved sum of 80.

## A key the type does not declare

Every type is closed. A write to a sealed value, or to a value of a `rec/defproven-in` type,
throws for a key that the type does not declare, before any check runs. The data of the throw
holds `:error` `:recognitum/undeclared-keys`, the type's name under `:type`, and the keys under
`:keys`. The constructors throw the same.

```clojure
(assoc account ::color "red")
;; ExceptionInfo: bank.account/Account has no field :bank.account/color. Its fields: :bank.account/owner :bank.account/balance :bank.account/reserved :bank.account/nickname
```

A draft accepts such a key. While the draft holds one:

- `rec/seal` of the draft throws an `ex-info` whose `:error` is `:recognitum/undeclared-keys`,
  before any check runs. A seal never drops a key.
- `rec/proves?` of the draft is false, whatever the draft remembers.
- `rec/check` does not read the key, and can answer `true`.

`(rec/clean d)` returns the draft `d` without those keys, remembering what `d` remembers. Code
that means to drop such keys calls it before the seal.

```clojure
(def noted (assoc draft ::color "red"))

(rec/seal noted)
;; ExceptionInfo: bank.account/Account has no field :bank.account/color. Its fields: :bank.account/owner :bank.account/balance :bank.account/reserved :bank.account/nickname
(rec/check noted rec/every)
;; => true
(rec/proves? noted rec/every)
;; => false
(rec/proves? (rec/clean noted) rec/every)
;; => true
(rec/sealed? (rec/seal (rec/clean noted)))
;; => true
```

[memory.md](memory.md) states what such a draft remembers.

## A write that fails

A write to a sealed value that fails throws an `ex-info` with the data that a failed
constructor or a failed seal gives: `:error` is `:recognitum/check-failed`, and the report of
the failed checks is beside it. [failures.md](failures.md) states the report. A write that
removes a required field fails in this way.

## What is not a write

- `empty` of a value or of a draft throws `UnsupportedOperationException`. A draft that holds
  nothing is `(rec/draft T)`.
- A function that builds another map from a value's entries, such as `select-keys` or
  `(into {} v)`, returns a plain map. A plain map proves nothing, whatever its entries.

```clojure
(rec/sealed? (into {} account))
;; => false
```

## A value of a displaced definition

A displaced definition is a definition of a type that a later definition replaced. A write to
one of its values follows other rules, which [redefinition.md](redefinition.md) states.

## Not promised

A write that changes nothing is not promised to return the very value it was given.
