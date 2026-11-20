# Asking a type's checks about plain data

The task: code needs the answer of a type's checks in a place where no value can be built, or
where none should be. A form is still being corrected. A sheet of rows must be accepted whole
or refused whole before the first row is written. A screen must show what would be valid after
a change that has not been made. Code that cannot ask the type's checks there needs a second
copy of the type's rules, and a copy can drift from the type.

The tool is the **probe**. `(rec/probe T fields)` asks the checks of the type `T` about the
plain map `fields`. It builds nothing and remembers nothing. It answers `true`, or a report of
everything that is wrong with the map. `rec/probe-all` asks about many maps in one pass.

## The solution: every mistake of a form in one answer

An order has lines, and a check that asks a catalogue whether it lists each line's product. A
**source** is a function that check bodies read with `rec/fetch` or `rec/fetch-each`; `listed`
is one, and `calls` records each call of it.

```clojure
(ns shop.intake
  (:require [clojure.string :as str]
            [recognitum.core :as rec]))

(def calls (atom []))

(defn listed
  "A source: for each sku, whether the catalogue lists it."
  [skus]
  (swap! calls conj skus)
  (zipmap skus (map #(contains? #{"tea" "pot" "cup" "kettle"} %) skus)))

(defn line? [x] (and (map? x) (string? (:sku x)) (pos-int? (:qty x)) (pos-int? (:price x))))

(defn subtotal [lines] (reduce + (map #(* (:qty %) (:price %)) lines)))

(rec/defproven Order [id customer lines ^:optional discount]
  rec/checks
  (id       [] "the id is a positive whole number" (pos-int? id))
  (customer [] "the customer is named" (and (string? customer) (not (str/blank? customer))))
  (lines    [] "the lines are a vector of sku, quantity and price"
    (and (vector? lines) (every? line? lines)))
  (discount [] "the discount is a whole number of cents" (nat-int? discount))

  (skus-listed []
    "the catalogue lists every sku"
    (every? true? (vals (rec/fetch-each listed (distinct (map :sku lines))))))
  (discount-within-subtotal []
    "the discount is no more than the subtotal"
    (rec/when-extant discount (<= discount (subtotal lines)))))

(defn form-errors
  "What to tell the person who filled in the form, before anything is built: one message for
  each field left out, each key that an Order does not have, and each check that the entries
  fail. Nil where `fields` would make an Order."
  [fields]
  (let [answer (rec/probe Order fields)]
    (when-not (true? answer)
      (let [{:keys [missing undeclared failed]} answer]
        (-> []
            (into (map #(str (name %) " is required")) (sort missing))
            (into (map #(str (name %) " is not a field of an order")) (sort undeclared))
            ;; A check that failed because it read an absent field is left out: the field
            ;; is already reported as required.
            (into (for [[_ {:keys [doc data]}] (sort-by key failed)
                        :when (not (:absent data))]
                    (str "check failed: " doc))))))))
```

The form below has three mistakes of three kinds: a field is left out, a key is misspelled,
and a rule is broken. One call reports all three:

```clojure
(def form {::id 7
           ::cusotmer "Ada"
           ::lines [{:sku "tea" :qty 2 :price 450}]
           ::discount 5000})

(form-errors form)
;; => ["customer is required"
;;     "cusotmer is not a field of an order"
;;     "check failed: the discount is no more than the subtotal"]
(form-errors (-> form (dissoc ::cusotmer) (assoc ::customer "Ada" ::discount 500)))
;; => nil
```

## What a report of a probe holds

A report is a map. `form-errors` reads three of its keys:

- `:missing` holds the keys of the required fields that the map lacks.
- `:undeclared` holds the keys of the map that are not keys of the type's fields.
- `:failed` maps the id of each failed check to its failure. Under a failure, `:doc` is the
  check's docstring, and `:data` is what the check's body returned in place of `true`. A check
  that read an absent field has the data `{:absent key}`.

[reference/failures.md](../reference/failures.md) states the whole report.

A probe reports the three kinds together. The constructor does not: it throws for a key that
is not a field's key before it runs any check. With the constructor, the person who filled in
the form would mend the misspelled key, submit again, and only then hear of the rest:

```clojure
(map->Order form)
;; ExceptionInfo: shop.intake/Order has no field :shop.intake/cusotmer. Its fields: :shop.intake/id :shop.intake/customer :shop.intake/lines :shop.intake/discount
```

## Why not a draft and `rec/check`

A draft is an unchecked map of a type, and `rec/check` of a draft also answers `true` or a
report, and seals nothing. A probe differs from it in three ways:

- **A key that the type does not declare.** A draft accepts the misspelled key. `rec/check` of
  the draft runs the checks and does not report that key, and `rec/seal` of the draft throws
  for it as the constructor does. A probe reports the key under `:undeclared`, beside the rest.
- **What the call leaves behind.** A draft remembers each check that passed on it. A probe
  builds nothing and remembers nothing.
- **Another answer from a source.** Only a probe takes the fourth argument that
  [a section below](#asking-with-another-answer-from-a-source) describes.

Code that goes on to build the value from the same data, in steps, wants the draft:
[drafts.md](drafts.md) shows what a draft is for.

## A dry run of an import

An importer takes a sheet of orders. It must import every row or name every bad row, before it
writes the first. `rec/probe-all` answers for each row, and the rows share the catalogue's
calls: the catalogue is asked once for the sheet. A loop that calls `map->Order` or
`rec/probe` on each row asks the catalogue once for each row.

```clojure
(defn problems
  "The rows that would not make an Order, from the answers of a probe of the rows: a map from
  each such row's number to the fields it lacks, the keys that an Order does not have, and
  the docstrings of the checks that fail on it."
  [answers]
  (into (sorted-map)
        (keep-indexed
         (fn [i answer]
           (when-not (true? answer)
             [(inc i)
              (let [failed (into (sorted-map)
                                 (for [[id {:keys [doc data]}] (:failed answer)
                                       :when (not (:absent data))]
                                   [id doc]))]
                (cond-> (select-keys answer [:missing :undeclared])
                  (seq failed) (assoc :failed failed)))])))
        answers))

(defn import-problems
  "A dry run of an import: what is wrong with each of `rows`, maps of an Order's fields.
  Empty where every row would import."
  [rows]
  (problems (rec/probe-all Order rows)))

(def sheet
  [{::id 11 ::customer "Ada" ::lines [{:sku "tea" :qty 2 :price 450}]}
   {::id 13 ::customer "Edsger" ::lines [{:sku "samovar" :qty 1 :price 9900}] ::dicsount 500}
   {::id 14 ::lines [{:sku "kettle" :qty 1 :price 3500}]}])

(reset! calls [])

(import-problems sheet)
;; => {2 {:undeclared #{::dicsount}
;;        :failed {::skus-listed "the catalogue lists every sku"}}
;;     3 {:missing #{::customer}}}
@calls
;; => [["tea" "samovar" "kettle"]]
```

Once the dry run is empty, the importer builds the orders with `map->Order`, or with one
`rec/seal-all` over a draft for each row, which also asks the catalogue once.

## Asking with another answer from a source

A check that reads a source judges the data by what the source answers now. Some questions are
about another state of the world: after a transaction commits, after a setting changes, or on
an earlier day. The fourth argument of a probe maps a source to a function that answers in the
source's place, for that call only. The docstrings of `rec/probe` and `rec/probe-all` name that
argument `overrides`, and each such function is an **override** of its source. The third
argument is the selection of checks to run, and
`rec/every` selects every check.

### Rows that are not committed yet

An upload adds new products and the orders for them, in one transaction. The catalogue does not
list the new products until the transaction commits, so each order for a new product fails
`skus-listed`, though the upload as a whole is sound. The function below asks the orders
against the catalogue as it will stand after the commit:

```clojure
(defn upload-problems
  "A dry run of an upload that adds the products `new-skus` and the orders `rows` in one
  transaction."
  [new-skus rows]
  (problems
   (rec/probe-all Order rows rec/every
                  ;; For this call only, `skus-listed` reads this function in place of
                  ;; `listed`: the catalogue's own answer, and true for each new product.
                  {listed (fn [skus]
                            (merge (listed skus)
                                   (zipmap (filter (set new-skus) skus) (repeat true))))})))

(upload-problems #{"samovar"}
                 [{::id 13 ::customer "Edsger" ::lines [{:sku "samovar" :qty 1 :price 9900}]}
                  {::id 15 ::customer "Ada" ::lines [{:sku "urn" :qty 1 :price 7000}]}])
;; => {2 {:failed {::skus-listed "the catalogue lists every sku"}}}
```

Once the dry run is empty, the code writes the products and builds the orders with the
constructor, which then reads the catalogue itself.

### A setting that is about to change, and the state of an earlier day

A refund is valid where a permission service says that the actor holds the grant for the
order, and that the amount is within the actor's limit.

```clojure
(def grants (atom #{["dana" :refund 42] ["eli" :refund 42]}))

(defn allowed
  "A source: for each key `[user action order-id]`, whether the user holds that grant."
  [ks]
  (zipmap ks (map #(contains? @grants %) ks)))

(defn refund-limit
  "A source: for each user, the largest refund in cents that the user may issue."
  [users]
  (select-keys {"dana" 5000 "eli" 1000} users))

(rec/defproven Refund [actor order-id amount]
  rec/checks
  (actor    [] (string? actor))
  (order-id [] (pos-int? order-id))
  (amount   [] (pos-int? amount))
  (may-refund [] (true? (rec/fetch allowed [actor :refund order-id])))
  (within-limit [may-refund] (<= amount (or (rec/fetch refund-limit actor) 0))))
```

An admin screen sets each clerk's refund limit. Before a supervisor saves a new limit, the
screen shows which of the refunds that wait for approval would pass under it. The limit is not
saved yet, and must not affect the refunds that other requests check meanwhile:

```clojure
(defn under-limit
  "What each of `refunds`, maps of a Refund's fields, would answer if the refund limit of
  `user` were `cents`: true or a report."
  [refunds user cents]
  (rec/probe-all Refund refunds rec/every
                 {refund-limit
                  (fn [users] (merge (refund-limit users) (select-keys {user cents} users)))}))

(def waiting [{::actor "eli" ::order-id 42 ::amount 2500}
              {::actor "eli" ::order-id 42 ::amount 900}])

(mapv true? (rec/probe-all Refund waiting))
;; => [false true]
(mapv true? (under-limit waiting "eli" 3000))
;; => [true true]
(mapv true? (under-limit waiting "eli" 500))
;; => [false false]
```

An audit job asks whether each refund of last month was allowed when it was issued. Grants
have been revoked since, so the checks fail today on refunds that were valid then. A stored
row is a plain map and proves nothing, so the question is asked again, with both sources
answered from a record of that day. The service is not called:

```clojure
(defn valid-on-the-day
  "What each of `refunds` answers under the grants and limits of an earlier day. `snapshot`
  holds that day's `:grants`, a set of `[user action order-id]`, and `:limits`, a map from
  user to cents."
  [refunds {:keys [grants limits]}]
  (rec/probe-all Refund refunds rec/every
                 {allowed      (fn [ks] (zipmap ks (map #(contains? grants %) ks)))
                  refund-limit (fn [users] (select-keys limits users))}))

(def issued [{::actor "dana" ::order-id 41 ::amount 1500}
             {::actor "eli" ::order-id 41 ::amount 300}])

(mapv true? (rec/probe-all Refund issued))
;; => [false false]
(mapv true? (valid-on-the-day issued {:grants #{["dana" :refund 41]}
                                      :limits {"dana" 5000 "eli" 1000}}))
;; => [true false]
```

### Why not `with-redefs`, a parameter, or a second copy of the rules

Code that has no probe asks about another state of the world in one of three ways, and each
has a cost:

- **`with-redefs` on the source** replaces the source for every thread while it is in force.
  In a running server, every request that is checked meanwhile is judged by the replacement.
  A draft that is checked under it remembers the pass, and later seals without a call of the
  real source. [reference/memory.md](../reference/memory.md) shows the same effect with a
  dynamic binding.
- **A parameter that says which state to read**, passed to every source. A check takes no
  argument but its type's fields, so the parameter becomes a field of every type, or a dynamic
  var that every source has to read.
- **A second copy of the rules**, written against the other state. The copy drifts from the
  type.

With the fourth argument of a probe, the checks are the type's own. No run but that probe
reads the replacement, on this thread or another. The probe makes no draft and no value, so
nothing remembers a check that passed under the replacement.

## The rules

The docstring of `rec/probe-all` states the rules of a probe in full: what `fields` may be,
which fields a selection reports as missing, what a probe answers for a type that
`rec/defproven-in` defined, and what it throws. Two of them decide whether a probe fits a task:

- For a type that `rec/defproven` defined, a probe with no third and no fourth argument
  answers `true` exactly when `rec/seal` of a draft that holds the map's entries would return
  a value. So a dry run that is empty means that the constructor will accept each row, as long
  as the sources answer the same.
- A probe answers; it does not prove. Code that needs a value builds one afterward.

[reference/sources.md](../reference/sources.md) states how many calls a source receives from
one `rec/probe-all`.

## Longer examples

In a checkout of the repository, `clojure -M:dev -m demo.orders` runs the import and the upload
on a fuller `Order`, and `clojure -M:dev -m demo.authz` runs the two refund cases. Each prints
its steps. Their sources are `dev/demo/orders.clj` and `dev/demo/authz.clj`.
