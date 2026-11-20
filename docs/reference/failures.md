# Failures: reports, thrown data and `:error` keywords

A failed check reaches the caller in one of two forms:

- **A report, returned.** `rec/check`, `rec/recheck` and `rec/probe` answer `true` or a report,
  and `rec/check-all`, `rec/recheck-all` and `rec/probe-all` answer a vector of such answers.
- **An `ex-info`, thrown.** A constructor, a write to a sealed value and `rec/seal` return a
  value or throw. The data of the throw is the report with two more keys, `:error` and `:type`.

Every `ex-info` that a call of the library throws to its caller on purpose holds a keyword
under `:error` in its data.
The last section lists all of them.

```clojure
(ns garden.plot
  (:require [recognitum.core :as rec]))

(rec/defproven Plot [crop rows ^:optional owner]
  rec/checks
  (crop  [] "the crop is named" (string? crop))
  (rows  [] "the rows are a positive number" (pos-int? rows))
  (owner [] "the owner is named" (string? owner))
  (fits-the-bed [] "a plot has at most 12 rows" (<= rows 12))
  (worth-fencing [fits-the-bed] "a fenced plot has at least 3 rows" (>= rows 3)))
```

## The report

A report is a map with these keys:

| Key | Holds | Present |
|---|---|---|
| `:failed` | A map from the id of each failed check to a map of `:data`, `:blocked` and, where the check has a docstring, `:doc`. | Always. |
| `:blocked` | The ids of the checks that did not run because a check they wait on failed. | Always. |
| `:missing` | The keys of the absent required fields. | Where there are any. In a report of `rec/check`, `rec/recheck` or a probe, those whose presence the selection asks. |
| `:pulled-back` | For each failed check that a `rec/except` removed and a wait ran anyway, the checks that waited on it under `:waited-on-by`, and a `:hint`. | Where there are any. |
| `:undeclared` | The keys of the map that the type does not declare. | In a report of `rec/probe` or `rec/probe-all`, where there are any. |

Under a failed check, `:data` is the check's **failure data**: what its body returned in place
of `true`, or `{:absent key}` for a read of an absent field, or `{:fetch-failed source :cause e}`
for a failed read from a source. `:blocked` under a failed check holds the checks that its
failure kept from running, directly or through another blocked check.

In the example, `rec/draft` makes a draft, which is an unchecked map of the type, and
`rec/every` is the selection that selects every check.

```clojure
(def draft (into (rec/draft Plot) {::crop "beans" ::rows 20}))

(rec/check draft rec/every)
;; => {:failed {::fits-the-bed {:data false
;;                              :doc "a plot has at most 12 rows"
;;                              :blocked #{::worth-fencing}}}
;;     :blocked #{::worth-fencing}}
(rec/probe Plot {::rows 2 ::color "green"})
;; => {:failed {::crop {:data {:absent ::crop} :doc "the crop is named" :blocked #{}}
;;              ::worth-fencing {:data false :doc "a fenced plot has at least 3 rows" :blocked #{}}}
;;     :blocked #{}
;;     :missing #{::crop}
;;     :undeclared #{::color}}
```

## The throw of a constructor, a write or a seal

Two errors concern a value's entries:

- **`:recognitum/undeclared-keys`** is thrown before any check runs, where the entries hold a
  key that the type does not declare. Its data holds the type's name under `:type` and the keys
  under `:keys`.
- **`:recognitum/check-failed`** is thrown where a check fails or a required field is absent.
  Its data is the report, with the type's name under `:type`. The checks run whatever is
  absent, so one throw names both: `:failed` holds the failed checks, and `:missing` the absent
  required fields.

The message names the type, counts the failed checks, and gives one line for each failed check:
its id, its docstring in parentheses, its failure data, and the checks it blocked.

```clojure
(map->Plot {::crop "beans" ::rows 20})
;; ExceptionInfo: garden.plot/Plot failed 1 check
;;   :garden.plot/fits-the-bed (a plot has at most 12 rows): false, which blocked :garden.plot/worth-fencing

(try (map->Plot {::crop "beans" ::rows 20})
     (catch clojure.lang.ExceptionInfo e (ex-data e)))
;; => {:error :recognitum/check-failed
;;     :type garden.plot/Plot
;;     :failed {::fits-the-bed {:data false
;;                              :doc "a plot has at most 12 rows"
;;                              :blocked #{::worth-fencing}}}
;;     :blocked #{::worth-fencing}}

(try (map->Plot {::crop "beans" ::rows 4 ::color "green"})
     (catch clojure.lang.ExceptionInfo e (ex-data e)))
;; => {:error :recognitum/undeclared-keys
;;     :type garden.plot/Plot
;;     :keys #{::color}}
```

`:type` holds the type's name as a symbol.

## The throw of `rec/seal-all`

`rec/seal-all` seals every draft in a shape of plain data, or none. Where any draft fails, it
throws one `ex-info` whose `:error` is `:recognitum/drafts-failed`. Under `:failures`, the data
maps the path of each draft that failed to the data that `rec/seal` would have thrown for that
draft. Under `:drafts`, it holds the shape with every draft in place. The docstring of
`rec/seal-all` states what a path is.

```clojure
(try (rec/seal-all {:north draft})
     (catch clojure.lang.ExceptionInfo e
       (let [{:keys [error failures]} (ex-data e)]
         [error (keys failures) (:error (get failures [:north]))])))
;; => [:recognitum/drafts-failed ([:north]) :recognitum/check-failed]
```

## What is not a failure report

An exception that a check body throws, other than a read of an absent field or a failed read
from a source, is not a failed check. It propagates as it is out of the call that ran the check,
and that call answers nothing for any value.

## Every `:error` keyword

A **displaced definition** is a definition of a type that a later definition replaced;
[redefinition.md](redefinition.md) states what refuses its values.

| `:error` | Thrown where |
|---|---|
| `:recognitum/check-failed` | A constructor, a write to a sealed value or a seal fails a check, or lacks a required field. |
| `:recognitum/undeclared-keys` | A constructor, a write to a value or a seal meets a key that the type does not declare. |
| `:recognitum/drafts-failed` | `rec/seal-all` or `rec/drafting-all` could not seal every draft. |
| `:recognitum/selects-nothing` | `rec/seal` is given a value of a `rec/defproven-in` type and a selection other than `rec/every` that selects nothing in the type. |
| `:recognitum/draft-selection` | `rec/seal` is given a draft and a selection other than `rec/every`. |
| `:recognitum/unknown-name` | A selection is or holds a keyword that names nothing, or a check id that the type it is used on lacks: see [selections.md](selections.md). |
| `:recognitum/not-a-selection` | A function that takes a selection is given something else. |
| `:recognitum/not-a-type` | A function that takes a value, a draft or a type's class is given something else. |
| `:recognitum/not-a-value` | A function that takes a value or a draft is given a type's class. |
| `:recognitum/not-a-draft` | `rec/seal` is given what is neither a draft nor a value; `rec/clean` is given a sealed value. |
| `:recognitum/not-a-map` | `rec/probe` or `rec/probe-all` is given, as the entries to ask about, something that is not a map. |
| `:recognitum/no-drafts` | `rec/draft`, `rec/clean` or `rec/drafting` is given a value of a `rec/defproven-in` type, or `rec/draft` its class. |
| `:recognitum/displaced` | A value of a displaced definition is written to, or one of its type's methods is called with it, or it is given to `rec/seal`, `rec/check`, `rec/recheck`, `rec/check-all` or `rec/recheck-all`. `rec/seal-all` lists such a value among its failures with this `:error`. |
| `:recognitum/displaced-constructor` | A constructor of a displaced definition is called, or an entry of an earlier `(rec/data-readers)` map; a draft of a displaced definition is given to `rec/seal`, `rec/check`, `rec/recheck`, `rec/check-all` or `rec/recheck-all`; `rec/probe` or `rec/probe-all` is given the class of one. `rec/seal-all` lists such a draft among its failures with this `:error`. |
| `:recognitum/no-current-definition` | `rec/draft` is given a value of a displaced definition whose type's name no longer names a definition. |
| `:recognitum/refused` | A definition form is refused. Where the form is refused as it expands, this `ex-info` is the cause of the compiler's exception. |

The docstring of each function names the keywords that the function throws and the condition
for each.

Three throws carry no `:error`, because they are not `ex-info`:

- `empty` of a value or of a draft throws `UnsupportedOperationException`.
- The class's own constructor, `(T. ...)`, throws `SecurityException`.
- A body macro (`rec/fetch`, `rec/fetch-each`, `rec/extant?`, `rec/when-extant`) written
  outside a check body throws `IllegalStateException` when the form expands, as the cause of
  the compiler's exception.

## Not promised

The wording of a message and the order of its lines are not promised. Code that handles a
failure reads `:error` and the rest of the data.
