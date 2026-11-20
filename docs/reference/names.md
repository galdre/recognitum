# What a definition names

Each defining macro makes names in the namespace where it is evaluated. Field keys, check ids
and concern ids are keywords in that namespace, and the type's class is in the package that
Java names after the namespace. This
page lists the names, and how another namespace writes each one.

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

## Not promised

- The names of the other classes that a definition generates, and their number.
- The names of the class's fields and of its methods beyond those of the interfaces it
  implements.
