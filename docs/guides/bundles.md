# One group of checks for several types

The task: several types hold the same kind of data, and the same rules apply to it in each. An
order has a shipping address, an order may have a billing address, and a depot has an address
of its own. The rules of an address should be written once.

The tool is the **bundle**: a group of checks over named **inputs**, defined once with
`rec/defchecks`. A type **binds** the bundle by saying how each input is read from the type's
fields.

## The solution

```clojure
(ns shop.address
  (:require [clojure.string :as str]
            [recognitum.core :as rec]))

(def postcode-forms
  {"US" #"\d{5}" "DE" #"\d{5}" "NL" #"\d{4} ?[A-Z]{2}"})

(rec/defconcern delivery "What the carrier needs before it takes a parcel.")

(rec/defchecks postal-address
  "The checks of a postal address."
  [street postcode country]
  rec/checks
  (street-given []
    "the address has a street"
    (and (string? street) (not (str/blank? street))))
  (country-served [] delivery
    "the country is one the shop ships to"
    (contains? postcode-forms country))
  (postcode-fits-country [country-served] delivery
    "the postcode has its country's form"
    (and (string? postcode) (boolean (re-matches (postcode-forms country) postcode)))))

(rec/defcopy billing-address postal-address
  {street-given          billing-street-given
   country-served        billing-country-served
   postcode-fits-country billing-postcode-fits-country})

(rec/defproven Order [id shipping ^:optional billing]
  postal-address
  (street   [] (:street shipping))
  (postcode [] (:postcode shipping))
  (country  [] (:country shipping))

  ^{:when-extant billing}
  billing-address
  (street   [] (:street billing))
  (postcode [] (:postcode billing))
  (country  [] (:country billing))

  rec/checks
  (id       [] "the id is a positive whole number" (pos-int? id))
  (shipping [] "the shipping address is a map" (map? shipping))
  (billing  [] "the billing address is a map" (map? billing))
  (billed-where-shipped [shop.address/billing-country-served]
    "the bill goes to the country that the parcel goes to"
    (rec/when-extant billing (= (:country billing) (:country shipping)))))

(rec/defproven Depot [name street postcode country]
  postal-address
  (street   [] street)
  (postcode [] postcode)
  (country  [] country)

  rec/checks
  (name     [] "the depot is named" (string? name))
  (street   [] "the street is text" (string? street))
  (postcode [] "the postcode is text" (string? postcode))
  (country  [] "the country is text" (string? country))
  (shop.address/country-served [] :override
    "a depot stands in the Netherlands"
    (= "NL" country)))
```

The checks of `postal-address` now run on an order's shipping address and on a depot's
address. `Depot` replaces one of them, `country-served`, as a section below describes. In the
example, an order whose shipping postcode does not fit its country fails
`postcode-fits-country`, and a depot in Germany fails the depot's own `country-served`. The id
of a bundle's check is a keyword in the namespace that defined the bundle, whatever type binds
it:

```clojure
(def order
  (map->Order {::id 7 ::shipping {:street "1 Canal St" :postcode "1012 AB" :country "NL"}}))

(assoc order ::shipping {:street "5 Hauptstr." :postcode "1011" :country "DE"})
;; ExceptionInfo: shop.address/Order failed 1 check
;;   :shop.address/postcode-fits-country (the postcode has its country's form): false
(map->Depot {::name "North" ::street "2 Kade" ::postcode "10115" ::country "DE"})
;; ExceptionInfo: shop.address/Depot failed 1 check
;;   :shop.address/country-served (a depot stands in the Netherlands): false, which blocked :shop.address/postcode-fits-country
```

The solution also defines a **concern**, `delivery`, with `rec/defconcern`. A concern is a mark
that a check carries: two checks of `postal-address` carry `delivery`, which follows their wait
vectors. [A section below](#concerns-selecting-checks-across-types) shows what a concern is for.

## Defining the bundle

`rec/defchecks` takes a name, an optional docstring, a vector of inputs, and clauses after
`rec/checks`. A clause is written as a check clause of a type is written, with the inputs in
place of the fields: in a body the inputs are locals. A wait in a bundle names another check
of the same bundle by its bare name, as `postcode-fits-country` names `country-served`.

The form defines a var for the bundle and a var for each check. The other forms name the
bundle and its checks through those vars.

## Binding the bundle in a type

A binding is the bundle's var, followed by one clause for each input: `(input [] expression)`.
The expression is written over the type's fields, and gives the input its value. `Order` reads
each input out of the map in its field `shipping`, and `Depot` gives each input a field of its
own.

- The checks sections of a type are its bindings and its `rec/checks` section, in any order.
- A check of a bundle reads the fields that its inputs' clauses read, so it waits on the shape
  checks of those fields. In `Order`, the three address checks wait on the shape check of
  `shipping`, and none of them runs on a shipping address that is not a map.
- An input whose clause reads an absent field is absent, and a check that reads an absent
  input fails. [reference/absence-and-nil.md](../reference/absence-and-nil.md) shows the
  failure, and how a clause passes an absent field on.
- Any other exception that an input's clause throws propagates out of the call that ran the
  check, as an exception from a check body does.

[reference/defproven.md](../reference/defproven.md#the-binding-of-a-bundle) states the rules of a
binding, and what a binding refuses.

## Binding one bundle twice

A type binds a bundle once. A second binding of the same bundle is refused:

```clojure
(rec/defproven Parcel [from to]
  postal-address
  (street [] (:street from)) (postcode [] (:postcode from)) (country [] (:country from))

  postal-address
  (street [] (:street to)) (postcode [] (:postcode to)) (country [] (:country to))

  rec/checks
  (from [] (map? from))
  (to   [] (map? to)))
;; ExceptionInfo: shop.address/Parcel: two bindings of a bundle are named shop.address/postal-address
```

`rec/defcopy` makes the second bundle. Its map gives a new name to every check of the bundle,
and the copy's checks keep their docstrings and their concerns. `Order` binds `postal-address`
for the shipping address and the copy `billing-address` for the billing address, so a failure
says which address is at fault:

```clojure
(assoc order ::billing {:street "" :postcode "12345" :country "US"})
;; ExceptionInfo: shop.address/Order failed 2 checks
;;   :shop.address/billed-where-shipped (the bill goes to the country that the parcel goes to): false
;;   :shop.address/billing-street-given (the address has a street): false
```

## A binding for an optional field

`^{:when-extant billing}` on a binding skips the binding's checks, as passing, while the
optional field `billing` is absent. `order` above has no billing address and is valid. A write
that adds the field runs the checks, as the last example shows.

Without `:when-extant`, the binding's checks would read absent inputs on an order that has no
billing address, and the order would fail.

## A wait on a bundle's check

An **own check** of a type is a check of its `rec/checks` section. An own check waits on a
bundle's check by naming the check's var with its namespace: `billed-where-shipped` names
`shop.address/billing-country-served`. The namespace is written
even where the bundle is defined in the type's own namespace, because a bare name in a wait
vector names an own check of the type. The bundle's var in a wait vector, written the same
way, names every check of the bundle.

## Replacing one check of a bundle in one type

`Depot` replaces `country-served`. In the type's `rec/checks` section, a clause that is named
by the bundle check's var, with its namespace, and that carries the flag `:override`, gives
that check a body over the type's fields. The check keeps its id and its concerns, and the
bundle's other checks still wait on it: above, the depot's failed `country-served` blocked
`postcode-fits-country`. Where the binding has `:when-extant`, the replacement is skipped with
the binding's other checks, as passing, while that field is absent.

A replacement may carry a further concern, beside those that it keeps. It then writes both
flags in one set after its wait vector, as in `#{:override customs}` for a concern `customs`. A
concern written after `:override`, outside a set, is refused.

## Concerns: selecting checks across types

A **concern** is a mark that `rec/defconcern` defines. A check carries a concern where the
concern's name, or its id, follows the clause's wait vector, as `delivery` does in two clauses
of `postal-address`. The id of `delivery` is the keyword `:shop.address/delivery`. A concern is
a **selection**: it selects the checks that carry it, in whatever type.
The bundle's var is a selection too, of the bundle's checks.

```clojure
(rec/checks-of delivery Order)
;; => #{::country-served ::postcode-fits-country
;;      ::billing-country-served ::billing-postcode-fits-country}
(rec/checks-of delivery Depot)
;; => #{::country-served ::postcode-fits-country}
(rec/checks-of billing-address Order)
;; => #{::billing-street-given ::billing-country-served ::billing-postcode-fits-country}
(rec/checks-of billing-address Depot)
;; => #{}
```

So code can run the delivery checks of a value without knowing its type:
`(rec/check x delivery)`. [reference/selections.md](../reference/selections.md) states what
each selection selects, and [checked-in-parts.md](checked-in-parts.md) uses concerns to say
which checks each user of a value needs.

## From another namespace

A namespace that requires `shop.address` as `address` binds `address/postal-address`, waits on
`address/country-served`, and selects with `address/delivery`.
[reference/names.md](../reference/names.md) lists the names that each form makes.

## A longer example

`dev/demo/orders.clj` in the repository binds an address bundle and its copy in an order that
has lines, a discount and a protocol. In a checkout, `clojure -M:dev -m demo.orders` runs it.
