# What a definition names

Each defining macro makes names in the namespace where it is evaluated. Field keys, check ids
and concern ids are keywords in that namespace, and the type's class is in the package that
Java names after the namespace. This
page lists the names, and how another namespace writes each one. It also compares what a
definition makes with what `defrecord` makes.

```clojure
(ns air-fleet.plane
  (:require [recognitum.core :as rec]))

(rec/defconcern safety "What the safety office asks of a plane.")

(rec/defchecks airworthy [hours]
  rec/checks
  (inspected [] "the plane was inspected within 100 flight hours" (< hours 100)))

(rec/defproven Plane [name hours]
  airworthy
  (hours [] hours)

  rec/checks
  (name  [] (string? name))
  (hours [] (nat-int? hours))
  (named-in-full [] safety "the name has at least two characters" (< 1 (count name))))

(def plane (map->Plane {::name "Spirit" ::hours 12}))
```

## The names

| Form | Names it makes, in `air-fleet.plane` |
|---|---|
| `(rec/defproven Plane [name hours] ...)`, and `rec/defproven-in` alike | The class `air_fleet.plane.Plane`, imported into the namespace as `Plane`. The vars `map->Plane` and `->Plane`. The tag `#air-fleet.plane/Plane`. For each field, a key, such as `:air-fleet.plane/name`. For each own check, an id, such as `:air-fleet.plane/named-in-full`. |
| `(rec/defchecks airworthy [hours] ...)` | The var `airworthy`, which holds the bundle. For each check, a var and an id, such as `inspected` and `:air-fleet.plane/inspected`. |
| `(rec/defcopy new-name bundle {...})` | The var `new-name`, and for each renamed check a var and an id, in the namespace of the copy. |
| `(rec/defconcern safety "...")` | The var `safety`, which holds the concern, and the id `:air-fleet.plane/safety`. |
| `(rec/defcontext name doc sel)` | The var `name`, which holds the selection `sel`. |

Three points follow from the table:

- **A field and its shape check share one keyword.** The check named after a field is the
  field's shape check, so `::name` is both the key of the field `name` and the id of its shape
  check.
- **The class's package is the namespace's name as Java writes it**, with each `-` as `_`. The
  tag, the keys and the ids keep the namespace's own spelling.
- **The type's name, as error data gives it under `:type`, is the symbol
  `air-fleet.plane/Plane`.**

```clojure
(.getName (class plane))
;; => "air_fleet.plane.Plane"
(pr-str plane)
;; => "#air-fleet.plane/Plane #:air-fleet.plane{:name \"Spirit\", :hours 12}"
(rec/checks-of rec/every Plane)
;; => #{:air-fleet.plane/name :air-fleet.plane/hours
;;      :air-fleet.plane/named-in-full :air-fleet.plane/inspected}
(= (rec/checks-of safety Plane) (rec/checks-of :air-fleet.plane/safety Plane))
;; => true
```

## From another namespace

A namespace that requires `air-fleet.plane` as `plane` writes the names like this:

```text
(ns air-fleet.hangar
  (:require [air-fleet.plane :as plane]
            [recognitum.core :as rec])
  (:import [air_fleet.plane Plane]))

(plane/map->Plane {::plane/name "Spirit" ::plane/hours 12})   ; the constructor and the keys
(rec/check a-draft ::plane/named-in-full)                     ; a check's id
(rec/proves? a-plane plane/safety)                            ; a concern, through its var
(rec/proves? a-plane ::plane/safety)                          ; a concern, by its id
(instance? Plane x)                                           ; the class, as imported
(instance? air_fleet.plane.Plane x)                           ; the class, by its full name
```

The alias does not reach the class: `plane/Plane` names a var, and no such var exists. A type
hint and `extend-protocol` name the class by its full name or by the name the import gives it.

A wait in a check clause names a bundle's check, or a whole bundle, by its qualified var:
`plane/inspected`, `plane/airworthy`. The docstring of `rec/defproven` states the rule.

## Names inside a body

In a check body and in a method body, the fields are locals. A field's name therefore hides any
var of the same name for the whole body, the vars of `clojure.core` included. In the type
above, the field `name` hides `clojure.core/name` in every body of `Plane`, so a body that
needs the function writes `clojure.core/name`.

```clojure
(rec/defproven Label [name]
  rec/checks
  (name [] (keyword? name))
  (short [] (< (count (clojure.core/name name)) 10)))

(rec/sealed? (map->Label {::name :fragile}))
;; => true
```

A macro that is used in a check body sees the fields in `&env`, as locals with their type hints.

A `deftype` that a check body defines does not see the fields in its methods, and a definition
is refused where such a method names a field. The body passes the field to the `deftype` as one
of the `deftype`'s own fields, or it uses `reify`, whose methods close over the body's locals.

## A name that is taken

A definition whose name already names a var or another class in the namespace is refused, and
leaves nothing. Evaluating a definition again under the same name is not such a case: it
redefines the type, as [redefinition.md](redefinition.md) describes.

## Compared with a record

A type is used much as a record is, and it is not built on `defrecord`: the library generates
the type's class, and a value is a map that is not a record. The table compares a record with
a value of a type that `rec/defproven` defined. In the table, `T` is the name of the record's
class or of the type, `f` is the name of a field, and `v` is the record or the value.

| Point | A record | A value of a `rec/defproven` type |
|---|---|---|
| What the definition makes | A class, imported into the namespace, and the vars `->T` and `map->T`. | The same, and a tag for printing. |
| The class's own constructor, `(T. ...)` | Makes a record. | Throws `SecurityException`. |
| A field's key | The unqualified keyword `:f`. | The keyword `:the.namespace/f`, which the defining namespace writes as `::f`. |
| `->T` | Takes every field in order, however many there are. | The same, and it runs every check. An optional field that it is given `nil` for is present and holds `nil`. |
| `map->T` of a map that lacks a field | Gives the field `nil`. | Throws for a required field. Leaves an optional field absent. |
| `map->T` of a map that holds a key that is not the key of a field | Keeps the key. | Throws. |
| Keyword lookup, `get`, destructuring, `keys`, `vals`, `seq`, `count`, `contains?`, `reduce-kv` | Read the record as a map, with the fields in the order of the definition. | The same. Destructuring names the qualified keys: `{::keys [f]}`. |
| A call of the record or the value as a function, `(v k)` | Throws: a record is not a function. | Returns what `(get v k)` returns. |
| A read of a field by Java interop, `(.f v)` | Returns the field. | Throws: the class has no such field. |
| `assoc` of a field | Returns a record. | Runs the checks that read the field. Returns a value of the type, or throws. |
| `assoc` of a key that is not the key of a field | Returns a record that holds the key. | Throws. |
| `dissoc` of a field | Returns a plain map. | Throws for a required field. Returns a value of the type for an optional field. |
| `merge`, `into` and `conj` onto the record or the value, and `update` of it | Return a record. | Return a value of the type, checked as [writes.md](writes.md) states, or throw. |
| `transient` | Throws. | Makes a transient, and `persistent!` of it is one checked write. |
| `empty` | Throws. | Throws. |
| `=` with a plain map of the same entries | False. | True, in both directions. |
| `=` with another record or value | True of a record of the same class with equal fields. | True of any map with equal entries, a value of another type included. |
| `hash` | Differs from the hash of a plain map of the entries. | Equals that map's hash. |
| `record?` | True. | False. |
| `map?`, and `(instance? T v)` | True. | True. |
| How it prints | `#the.namespace.T{:f 1}` | `#the.namespace/T #:the.namespace{:f 1}` |
| `str` | The class's name and a hash code, unless the definition gives `toString`. | The printed form, unless the definition gives `toString`. |
| Reading the printed text | The Clojure reader reads it with no setup, and `clojure.edn` does not read it. | Either reader reads it once the program gives the tag a reader, and the read runs every check: [printing-and-reading.md](printing-and-reading.md). |
| Metadata | `with-meta` returns a record, and a write keeps the metadata. | `with-meta` returned a sealed value, and a write kept the metadata, where this was tried. [printing-and-reading.md](printing-and-reading.md) says what is not promised. |
| Protocols and interfaces in the definition | Each is followed by its methods, and in a method body the fields are locals. | The same, written after the checks. Of the methods of `Object`, only `toString` may be given: [the guide to methods](../guides/methods.md). |
| A protocol extended to the class from outside the definition | Answers for a record. | Answers for a value. |
| Java serialization | A record comes back as a record. | A value comes back as a plain map, which is not sealed. |
| The definition evaluated again | Makes a new class. A record of the earlier class still reads and writes, and does not equal a record of the new class. | Makes a new class. A value of the earlier class still reads and still equals a map of its entries. It is not sealed, and a write to it throws: [redefinition.md](redefinition.md). |

The example compares the plane above with a record of the same fields:

```clojure
(defrecord Glider [name hours])

(def glider (->Glider "Spirit" 12))

(defn error-of
  "The `:error` of the ex-info that calling `f` throws, or nil where `f` returns."
  [f]
  (try (f) nil
       (catch clojure.lang.ExceptionInfo e (:error (ex-data e)))))

[(record? glider) (record? plane) (map? glider) (map? plane)]
;; => [true false true true]
[(= glider {:name "Spirit" :hours 12}) (= plane {::name "Spirit" ::hours 12})]
;; => [false true]
[(record? (assoc glider :wings 2)) (error-of #(assoc plane ::wings 2))]
;; => [true :recognitum/undeclared-keys]
[(record? (dissoc glider :hours)) (error-of #(dissoc plane ::hours))]
;; => [false :recognitum/check-failed]
```

A type that `rec/defproven-in` defined compares with a record as the table states, except in
the rows on checks. Its constructors and its writes run no check, so `map->T` leaves any
absent field absent, and `dissoc` of any field returns a value of the type. Its constructors
and its writes still throw for a key that is not the key of a field. A read of its printed
text runs no check, and its values are never sealed: `(rec/proves? v sel)` asks what a value
has passed.

## Not promised

- The names of the other classes that a definition generates, and their number.
- The names of the class's fields and of its methods beyond those of the interfaces it
  implements.
