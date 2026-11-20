# Absent fields and nil

A field is **absent** from a value when the value has no entry under the field's key. A field
that holds `nil` is present. No function of the library treats `nil` as absence.

A field marked `^:optional` may be absent. Every other field is **required**.

```clojure
(ns travel.trip
  (:require [recognitum.core :as rec]))

(defprotocol Describe
  (describe [trip]))

(rec/defproven Trip [from to ^:optional via]
  rec/checks
  (from [] "the start is named" (string? from))
  (to   [] "the end is named" (string? to))
  (via  [] "the stop is named" (string? via))
  (goes-somewhere [] "the start and the end differ" (not= from to))
  (stop-on-the-way [] "the stop is neither end" (rec/when-extant via (not (#{from to} via))))

  Describe
  (describe [_] (str from " to " to (when via (str " by " via)))))
```

## An optional field

A check named after a field is the field's **shape check**. The shape check of an optional field
passes where the field is absent. Where the field holds `nil`, the field is present, and its
shape check runs on `nil`.

```clojure
(def trip (map->Trip {::from "Oslo" ::to "Bergen" ::via "Voss"}))

(contains? (dissoc trip ::via) ::via)
;; => false
(assoc trip ::via nil)
;; ExceptionInfo: travel.trip/Trip failed 1 check
;;   :travel.trip/via (the stop is named): false, which blocked :travel.trip/stop-on-the-way
```

So code that means "no stop" leaves the key out, or removes it with `dissoc`. `->Trip` takes
every field in order, so a `nil` passed to it for an optional field is a present `nil`. Of the
two constructors, only `map->Trip` can make a value that lacks an optional field.

```clojure
(->Trip "Oslo" "Bergen" nil)
;; ExceptionInfo: travel.trip/Trip failed 1 check
;;   :travel.trip/via (the stop is named): false, which blocked :travel.trip/stop-on-the-way
```

## A read of an absent field

In a check body, a read of an absent field throws, and the throw fails the check with the
failure data `{:absent key}`, where `key` is the field's key. `(rec/extant? f)` answers whether
the field `f` is present, and `(rec/when-extant f body...)` passes where `f` is absent. Above,
`stop-on-the-way` asks before it reads. The check `short-stop` below reads without asking, so it
fails on every value that lacks the stop:

```clojure
(rec/defproven Leg [from ^:optional via]
  rec/checks
  (from [] (string? from))
  (via  [] (string? via))
  (short-stop [] "the stop has a short name" (< (count via) 4)))

(map->Leg {::from "Oslo"})
;; ExceptionInfo: travel.trip/Leg failed 1 check
;;   :travel.trip/short-stop (the stop has a short name): {:absent :travel.trip/via}
```

`rec/extant?` and `rec/when-extant` are written in a check body, or in an input clause of a
binding of a bundle, and only in call position: `(map rec/extant? ...)` is refused. Unlike a
read of a source, each may stand inside a function that the body builds (`fn`, `#(...)`, `for`,
`lazy-seq`, `delay`) and inside `locking`.

A method body differs from a check body: in a method body the local of an absent field is
`nil`, and a read of it does not throw.

```clojure
(describe (map->Trip {::from "Oslo" ::to "Bergen"}))
;; => "Oslo to Bergen"
```

## A required field

A constructor, a write or a seal of a `rec/defproven` type fails where a required field is
absent. The data of the throw names the field under `:missing`. The field's shape check fails
with `{:absent key}`. Every other check that reads the field waits on that shape check, so it
is blocked, and so are the checks that wait on it. Where the field has no shape check, each
check that reads the field fails with `{:absent key}`.

```clojure
(try (map->Trip {::from "Oslo"})
     (catch clojure.lang.ExceptionInfo e
       (select-keys (ex-data e) [:error :missing :blocked])))
;; => {:error :recognitum/check-failed
;;     :missing #{::to}
;;     :blocked #{::goes-somewhere ::stop-on-the-way}}
(dissoc trip ::to)
;; ExceptionInfo: travel.trip/Trip failed 1 check and lacks the required field :travel.trip/to
;;   :travel.trip/to (the end is named): {:absent :travel.trip/to}, which blocked :travel.trip/goes-somewhere, :travel.trip/stop-on-the-way
```

A required field that holds `nil` is present, so nothing reports it as missing. Its shape check
runs on `nil`:

```clojure
(try (map->Trip {::from "Oslo" ::to nil})
     (catch clojure.lang.ExceptionInfo e
       [(:missing (ex-data e)) (get-in (ex-data e) [:failed ::to :data])]))
;; => [nil false]
```

## A draft that lacks a required field

A **draft** is an unchecked map of a type, made with `rec/draft` and sealed into a value with
`rec/seal`. A draft may lack any field. These functions answer for a draft that lacks a required
field:

- `(rec/seal d)` throws as the constructor does.
- `(rec/check d sel)` and `(rec/recheck d sel)` answer a report, never `true`, while `d` lacks a
  required field whose presence the selection `sel` asks. The report names each such field
  under `:missing`. The docstring of `rec/check` states which selections ask the presence of
  which fields.
- `(rec/proves? d sel)` is false, whatever `sel` selects, while `d` lacks any required field.
  It still throws where `sel` is or holds a keyword that names no check of the type, as
  [selections.md](selections.md) states.

```clojure
(def started (assoc (rec/draft Trip) ::from "Oslo"))

(rec/check started ::from)
;; => true
(:missing (rec/check started ::goes-somewhere))
;; => #{::to}
(rec/proves? started ::from)
;; => false
```

The second call asks the presence of `to` because `goes-somewhere` reads `to`. The first call
asks the presence of no field but `from`.

## A value of a `rec/defproven-in` type

`rec/defproven-in` defines a type whose constructors and writes check nothing, so a value of
such a type may lack a required field. `rec/check`, `rec/recheck` and `rec/proves?` answer for
it as they answer for a draft, and `(rec/seal v sel)` throws while `v` lacks a required field.

```clojure
(rec/defproven-in Plan [from to]
  rec/checks
  (from [] (string? from))
  (to   [] (string? to)))

(def plan (map->Plan {::from "Oslo"}))

(rec/check plan ::from)
;; => true
(rec/proves? plan ::from)
;; => false
(rec/seal plan ::from)
;; ExceptionInfo: travel.trip/Plan failed 1 check and lacks the required field :travel.trip/to
;;   :travel.trip/to: {:absent :travel.trip/to}
```

## An input of a bundle

A **bundle** is a group of checks over named inputs, defined with `rec/defchecks`. A type that
binds the bundle gives one clause for each input. An input is absent where its clause reads an
absent field, and a read of an absent input fails the bundle's check with `{:absent :input}`,
where `:input` is the input's name as a keyword. `^{:when-extant field}` on the binding skips
the binding's checks, as passing, while that optional field is absent.

```clojure
(rec/defchecks positive [n]
  rec/checks
  (above-zero [] "the number is above zero" (pos? n)))

(rec/defproven Fare [zone ^:optional discount]
  positive
  (n [] discount)

  rec/checks
  (zone     [] (keyword? zone))
  (discount [] (number? discount)))

(map->Fare {::zone :city})
;; ExceptionInfo: travel.trip/Fare failed 1 check
;;   :travel.trip/above-zero (the number is above zero): {:absent :n}

(rec/defproven Ticket [zone ^:optional discount]
  ^{:when-extant discount}
  positive
  (n [] discount)

  rec/checks
  (zone     [] (keyword? zone))
  (discount [] (number? discount)))

(def ticket (map->Ticket {::zone :city}))

(assoc ticket ::discount -5)
;; ExceptionInfo: travel.trip/Ticket failed 1 check
;;   :travel.trip/above-zero (the number is above zero): false
```

In an input clause, `rec/extant?` and `rec/when-extant` take a field. A clause that guards its
read with `rec/when-extant` gives the input the value `true` where the field is absent, so the
input is present. To pass an absent field on as an absent input, the clause reads the field:
`(n [] discount)`.

## Not promised

- No default is filled in for an absent field: a value holds the entries it was given.
- Nothing reports a value of a `rec/defproven-in` type that lacks a required field until a
  call asks: the constructor and the writes of such a type check nothing.
