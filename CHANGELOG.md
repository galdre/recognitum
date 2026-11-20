# Changelog

## 0.3.1 (2026-11-20)

In this section, a **displaced** definition is a definition of a type that a later definition
of the same name replaced. A **selection** is what `rec/check`, `rec/seal` and `rec/proves?`
take to say which checks they mean: `rec/every`, a check's id, a concern, or a combination of
these.

### Added

- `(rec/selects-nothing? sel x)` answers whether `sel` selects no check, and asks no required
  field's presence, in the type of `x`. `x` is a value, a draft or a type's class.
- The clj-kondo hook reports the three forms of a clause's flags that the macros now refuse
  (see Fixed), where it can tell: `:recognitum/misplaced-flag` for a flag written after the
  docstring or after another flag, and for a check whose whole body is a concern, and
  `:recognitum/undeclared-concern` for `::name` where `name` is a var of another namespace. It
  cannot tell for a concern of a namespace that clj-kondo has not analyzed.
- `recognitum.record/define-type`, the function below the macros, takes `:instead`: a string
  that closes the message of the type's class constructor, which throws when code calls it.
  The string tells the caller what to call in place of the constructor. An `:instead` that is
  not a string is refused, and so is one of more than 10000 characters.

### Changed

- The README is now a short introduction. The rest moved to `docs/`: a tutorial
  ([docs/tutorial.md](docs/tutorial.md)), guides that each work through one task
  ([docs/guides/](docs/guides/README.md)), a reference of the rules that span several functions
  ([docs/reference/](docs/reference/README.md)), a statement of what holding a value proves
  ([docs/guarantee.md](docs/guarantee.md)), and a description of the layers below
  `recognitum.core` ([docs/internals.md](docs/internals.md)).
- A function that refuses a `rec/defproven-in` value without proof must ask the value's type
  as well as its proof: `(and (instance? Potion x) (rec/proves? x sel))`. `rec/proves?` does
  not ask which type a value has, so it is also true of a proven value of another type. The
  gate in the README of 0.3.0 and in `demo.potion` asked `rec/proves?` alone; code copied from
  it needs the `instance?` test. [docs/guides/sinks.md](docs/guides/sinks.md) explains both
  questions.
- The class constructor of a type, `(Heist. ...)`, still throws a `SecurityException`. Its
  message now names the functions that make a value: "make a value with
  casino.heist/map->Heist or casino.heist/->Heist".
- The refusal of a check's body names the check or the input clause that the body is in, after
  the type and before the line: "casino.heist/Heist, check crew, line 12: ...".
- The refusal of a probe of a displaced definition's class ends "Probe the class that Heist
  names now in casino.heist".
- The clj-kondo hook's report of an unqualified wait on a bundle says how to qualify the wait,
  as its report of an unqualified wait on a bundle's check does.

### Fixed

- `rec/seal-all` reports a `rec/defproven-in` value that lacks a required field with the absent
  fields under `:missing`, as `rec/seal` does. In 0.3.0 the entry in `:failures` had no
  `:missing`.
- `rec/seal-all` gives no `:pulled-back` entry in the failure of a `rec/defproven-in` value,
  as `rec/seal` gives none. In 0.3.0, under a selection built with `rec/except`, the failure
  could hold a `:pulled-back` entry that named no check.
- `rec/seal-all` seals the drafts in a queue (a `clojure.lang.PersistentQueue`), and the queue
  comes back as a vector. In 0.3.0 the queue came back as a list with its drafts unsealed, and
  nothing was thrown. The docstrings of `rec/seal-all` and `rec/drafting-all` now state which
  collections are searched for drafts, and that nothing else is: a draft inside a Java
  collection, an array, an atom or an object of a `deftype` comes back unsealed.
- A source that throws `InterruptedException` still fails its check with `:fetch-failed`, and
  the thread's interrupt flag is now set afterward. In 0.3.0 the flag was left cleared.
- The refusal of a body in a bundle reads "an input", where it read "a input".
- Under clj-kondo's `:missing-docstring` linter, a check that `rec/defcopy` copies from a
  check with a docstring draws no warning. A check that is copied from a check without a
  docstring still draws one.
- This file's section for 0.3.0 had entries that were wrong or incomplete, and lacked one
  entry on `rec/drafting-all`. They are corrected below.

Each of the fixes below changes what a call returns or throws, so each shows the call in 0.3.0
and now, and what to write where code relied on the old result. The examples use two concerns,
`permission` and `audit`, that the namespace `app.perms` defines with `rec/defconcern`.

- A flag (a concern or `:override`) that is written after a clause's docstring, or after the
  clause's first flag, is refused. 0.3.0 read it as a statement of the body, so the check did
  not carry the concern.

  ```clojure
  (allowed [] "doc" permission (some? actor))
  (allowed [] permission audit (some? actor))
  ;; 0.3.0: both accepted; the first did not carry permission, the second did not carry audit
  ;; 0.3.1: both refused when the type is defined
  ```

  Write the flags after the waits and before the docstring, and several flags as one set:
  `(allowed [] permission "doc" (some? actor))` and
  `(allowed [] #{permission audit} (some? actor))`.

- `::name` as a flag is refused where `name` is a concern that another namespace defines and
  this namespace refers. `::name` is then a keyword of this namespace, and it is not the
  concern's id. 0.3.0 accepted it, and the check carried no concern.

  ```clojure
  (ns app.grant
    (:require [app.perms :refer [permission]]
              [recognitum.core :as rec]))

  (c [] ::permission (some? actor))
  ;; 0.3.0: accepted; c carried no concern
  ;; 0.3.1: refused when the type is defined
  ```

  Write the concern's symbol or its id: `(c [] permission (some? actor))` or
  `(c [] :app.perms/permission (some? actor))`.

- A check whose whole body is a concern is refused. 0.3.0 accepted it as a check that carried
  no concern and failed on every value.

  ```clojure
  (allowed [] permission)
  (allowed [] "doc" :app.perms/permission)
  ;; 0.3.0: both accepted; allowed carried no concern, and it failed on every value,
  ;;        because its body returned the concern and not true
  ;; 0.3.1: both refused when the type is defined
  ```

  Write the body after the flag: `(allowed [] permission (some? actor))`.

- `rec/seal` of a `rec/defproven-in` value by a selection that selects nothing in the value's
  type throws `:recognitum/selects-nothing` before any check runs. A selection selects nothing
  in a type where it selects no check of the type and asks no required field's presence.
  `rec/seal-all` reports the refusal at the value's path, and `rec/proves?` by such a selection
  is false. `rec/every` is never refused. 0.3.0 returned the value from such a seal, and
  `rec/proves?` by the selection was then true, though the selection had selected no check.

  ```clojure
  (rec/defproven-in Label [text]
    rec/checks
    (text [] "the text is written" (string? text)))

  (def label (map->Label {::text "Courage"}))

  (rec/seal label permission)
  ;; 0.3.0: returned label
  ;; 0.3.1: throws :recognitum/selects-nothing
  (rec/proves? label permission)
  ;; 0.3.0: true after that seal
  ;; 0.3.1: false
  (rec/seal-all [label] permission)
  ;; 0.3.0: [label]
  ;; 0.3.1: throws :recognitum/drafts-failed, with the refusal under [0] in :failures
  ```

  Where a check of the type should carry the concern, write the concern after that check's
  waits. Where the type has nothing to prove for the concern, give the type a check that
  carries the concern and passes: `(nothing-to-prove [] permission "Why." true)`.

- A definition displaces the earlier definition of its name in three cases where 0.3.0 left
  the earlier definition current: the name was unmapped (`ns-unmap`) before the type was
  defined again; the namespace was removed (`remove-ns`) and its code was evaluated again, as
  a reload by `clojure.tools.namespace` does; or a `defrecord` of the same name was evaluated
  in between. In 0.3.0, a value of the earlier definition then counted as proven under the
  current definition.

  ```clojure
  (def old (map->Payment {::amount 5}))
  (def held map->Payment)
  (ns-unmap *ns* 'Payment)
  ;; the form that defines Payment is evaluated again

  (rec/sealed? old)
  ;; 0.3.0: true
  ;; 0.3.1: false
  (assoc old ::amount 6)
  ;; 0.3.0: a sealed value
  ;; 0.3.1: throws :recognitum/displaced
  (held {::amount 5})
  ;; 0.3.0: a sealed value
  ;; 0.3.1: throws :recognitum/displaced-constructor
  ```

  Prove the value under the current definition, `(rec/seal (rec/draft old))`, and call the
  current `map->Payment`.

- `rec/check`, `rec/recheck`, `rec/check-all` and `rec/recheck-all` throw
  `:recognitum/displaced` for a value of a displaced definition of a `rec/defproven` type, as
  a write to such a value does. 0.3.0 answered true.

  ```clojure
  (def old (map->Payment {::amount 5}))
  ;; the form that defines Payment is evaluated again

  (rec/check old rec/every)
  ;; 0.3.0: true
  ;; 0.3.1: throws :recognitum/displaced
  ```

  Prove the value under the current definition first: `(rec/seal (rec/draft old))`.

- The same four functions throw `:recognitum/displaced-constructor` for a draft of a displaced
  definition, as a seal of such a draft does. 0.3.0 ran the displaced definition's checks.

  ```clojure
  (def d (assoc (rec/draft Payment) ::amount 5))
  ;; the form that defines Payment is evaluated again

  (rec/check d rec/every)
  ;; 0.3.0: true, or a report of the displaced definition's checks that failed
  ;; 0.3.1: throws :recognitum/displaced-constructor
  ```

  Make a draft of the current definition from the old draft's entries:
  `(into (rec/draft Payment) d)`.

- `rec/check-all` and `rec/recheck-all` throw for a whole batch that holds such a value or
  such a draft. 0.3.0 answered for each element.

  ```clojure
  (rec/check-all [current-draft old] rec/every)
  ;; 0.3.0: [true true], an answer for each element
  ;; 0.3.1: throws :recognitum/displaced, and answers for no element
  ```

  Before the call, replace each displaced element as the two entries above say.

- `rec/seal` of a value of a displaced definition of a `rec/defproven` type throws
  `:recognitum/displaced`, where it threw `:recognitum/not-a-draft`.

  ```clojure
  (rec/seal old)
  ;; 0.3.0: throws ex-info whose :error is :recognitum/not-a-draft
  ;; 0.3.1: throws ex-info whose :error is :recognitum/displaced
  ```

  Code that matched `:recognitum/not-a-draft` for this case must match
  `:recognitum/displaced`.

- `rec/proves?` and `rec/seal` of a sealed value read the selection they are given. 0.3.0 did
  not read it: `rec/proves?` answered true and `rec/seal` returned the value, whatever they
  were given. They now throw
  `:recognitum/unknown-name` for a keyword that names no check of the value's type, no concern
  and no bundle check, and `:recognitum/not-a-selection` for anything else that is not a
  selection. `rec/proves?` of a draft that lacks a required field throws for them too, where
  it answered false. `rec/proves?` still answers false, whatever it is given as the selection,
  for a value of a displaced definition, a class and a plain map.

  ```clojure
  (def paid (map->Payment {::amount 5}))

  (rec/proves? paid ::typo)
  ;; 0.3.0: true
  ;; 0.3.1: throws :recognitum/unknown-name
  (rec/proves? paid 42)
  ;; 0.3.0: true
  ;; 0.3.1: throws :recognitum/not-a-selection
  (rec/seal paid ::typo)
  ;; 0.3.0: paid
  ;; 0.3.1: throws :recognitum/unknown-name
  (rec/proves? (rec/draft Payment) ::typo)
  ;; 0.3.0: false
  ;; 0.3.1: throws :recognitum/unknown-name
  ```

  Pass a selection: `rec/every`, the id of a check of the value's type, a concern, or a
  combination of these. The id of another type's check is an unknown name.

- `rec/proves?` is false for a draft that holds a key its type does not declare, and
  `rec/proven-concerns` of such a draft is `#{}`. 0.3.0 answered both as if the draft did not
  hold the key.

  ```clojure
  (def d (assoc (rec/draft Payment) ::amount 5))
  (rec/check d rec/every)
  ;; => true

  (rec/proves? (assoc d :stray 1) rec/every)
  ;; 0.3.0: true
  ;; 0.3.1: false
  ```

  Remove the key before asking: `(rec/proves? (rec/clean d) rec/every)`, or `dissoc` the key.

## 0.3.0 (2026-11-12)

### Added

- `rec/probe` and `rec/probe-all` ask whether a map would make a valid value of a type, without
  making one. They answer what `rec/check` answers of a fresh draft holding the map's entries,
  `true` or a report, with the keys the type does not declare under `:undeclared`. For a
  `rec/defproven-in` type, which has no drafts, they answer what `rec/check` answers of a
  value holding the map's declared entries. They read any map (a plain map, a record, a draft
  or a value of any type) and remember nothing. An optional map of overrides answers in a
  source's place for that call only. `probe-all` runs over a batch of maps in one pass.
- A required field's presence is a check of its own, with no name, part of the field's shape.
  A selection selects it as it selects a shape check that reads only that field and no source:
  `rec/every`, `rec/shape` and `rec/pure` select every field's, `(rec/reading ::f)` selects
  `f`'s, a check or a concern selects none, and `rec/union` and `rec/except` combine them as
  they combine checks, so `(rec/except rec/every (rec/reading ::b))` selects every presence
  check but `b`'s. Every check waits on the presence checks of the required fields it reads,
  and such a wait never keeps it from running.
- `rec/check`, `rec/recheck`, `rec/check-all` and `rec/recheck-all` report under `:missing`
  the required fields that a draft or a `rec/defproven-in` value lacks whose presence the
  selection asks: where it selects the field's presence check, or a check that waits on it.
  So a check or a concern asks the presence of the fields that its checks, and the checks
  they wait on, read.
- A clause names a concern by its symbol as well as by its keyword: `(may-cast [waits]
  permission body)`, `(may-cast [waits] perms/permission "doc" body)`, `#{permission ::audit}`.
- The clj-kondo hook reads a concern's symbol as the concern, and reports a symbol that names
  no concern where it can tell: one that names nothing, one that names a bundle or a bundle's
  check, and one that names any other var of a namespace clj-kondo has analyzed before. It
  cannot tell for a plain var of a file it lints for the first time.
- The README's section on probes states the problems a probe solves, with five worked examples
  in the demos: the messages for a form, a dry run of an import, and three that answer a source
  from elsewhere (rows not committed yet, a setting about to change, the grants and limits of an
  earlier day). `demo.heist-run` shows `rec/probe` and `rec/probe-all`.

### Changed

- The README and docstring examples use a ballot and a ballot box.

### Breaking

- `:recognitum/missing-fields` is gone. A seal, a constructor or a write that fails throws
  `:recognitum/check-failed` whether a check failed or a required field is absent. It runs
  the checks either way: `:failed` holds the failed checks, empty where only fields are absent,
  and `:missing` holds the absent required fields, and is left out where none is absent. Code
  that matched `:recognitum/missing-fields` must match `:recognitum/check-failed` and read the
  fields under `:missing`, where 0.2.0 gave them under `:keys`. The message reads "lacks the
  required field" where it read "needs the field".
- A run whose selection asks the presence of a field that a draft or a `rec/defproven-in` value
  lacks answers a report, not `true`, even where every check it runs passes:
  `{:failed {} :blocked #{} :missing #{...}}`.
- `rec/proves?` answers false for every selection while a required field is absent, so
  `rec/proven-concerns` answers `#{}`.
- `rec/seal-all` reports a value of a displaced definition of a `rec/defproven` type at its path
  with `:recognitum/displaced`, and gives it back in `:drafts` as it is. Before, it returned
  such a value as it was.
- `rec/drafting-all` gives `f` a value of a displaced definition of a `rec/defproven` type whose
  name names no definition as it is, and the seal reports it. Before, it threw
  `:recognitum/no-current-definition` before calling `f`.
- `rec/drafting-all` throws `:recognitum/drafts-failed` for a sealed value that holds, in a
  field, a value of a displaced definition of a `rec/defproven` type: its seal reports that
  value at the field's path with `:recognitum/displaced`. Before, it returned.
- A symbol after a clause's waits, with more forms after it, is read as a flag and must name a
  concern. In 0.2.0, `(check [] x body)` evaluated `x` as a statement of the body,
  `(check [] x "doc" body)` also dropped the docstring, and `(check [] shop body)` left the
  check without the concern `shop`, each without an error. A symbol that names no concern
  there is refused with a message that names it and the clause.
- A concern's symbol on an input clause is refused, as its keyword is.

## 0.2.0 (2026-11-10)

### Added

- `rec/defproven-in` defines a type from the same form as `rec/defproven`, whose constructors
  and writes check nothing. A value carries the checks that passed on it, `rec/proves?` asks
  what it passed, and `rec/sealed?` is always false for it. `rec/draft`, `rec/clean` and
  `rec/drafting` refuse such a type.
- `rec/defcontext` defines a var that holds a selection, with a docstring.
- `(rec/seal v sel)` seals a `rec/defproven-in` value against a selection and returns the
  value itself. For a draft, `sel` must be `rec/every`, or the seal throws.
- `(rec/seal-all shape sel)` seals each `rec/defproven-in` value in `shape` against `sel`;
  drafts still seal against every check. `rec/drafting-all` leaves such values as they are.
- `rec/recheck-all`: `rec/recheck` over a batch of values, in one pass.
- `rec/defchecks` and `rec/defcopy` take an optional docstring after the name. A copy's checks
  keep the docstrings of the bundle's checks.
- A clause's concerns and `:override` are written after its waits: `(may-write [waits]
  ::permission body)`, `#{::permission ::audit}` for several, `(perms/may-write [waits]
  :override body)`.
- The clj-kondo hook covers `rec/defproven-in` and `rec/defcontext`, gives the vars of a
  concern, a check and a context their docstrings, reports a malformed `rec/defcopy`, and
  reports metadata on a clause and a flag in the wrong place (`:recognitum/misplaced-meta`,
  `:recognitum/clause-flag`).
- `rec/defproven-in` and `rec/defcontext` carry `:style/indent`. The README lists the cljfmt
  rules for every definition macro.
- A second demo, `demo.potion`, and the walkthroughs `demo.authz` and `demo.orders`.

### Changed

- `rec/defchecks` and `rec/defcopy` indent as `defn` does.
- `seal-all` and `drafting-all` keep the metadata of the lists and sequences they walk.
- The demos moved from `recognitum.*` to `demo.*` under `dev/demo/`.

### Fixed

- `rec/sealed?` and `rec/proves?` answer false for a sorted map whose keys are not keywords.
  They threw `ClassCastException` before.

### Breaking

- `^::concern` and `^:override` on a clause are refused. Write them after the waits.
- Metadata on a clause, on its name, on its waits or on a section's head is refused. In
  0.1.1, a concern written on a clause's name was dropped without an error.
- A concern or `:override` on an input clause is refused.
- A keyword or a set of keywords after a clause's waits, with more forms after it, is read as
  the clause's flags. A keyword that is not a concern or `:override` is refused.
- A type's class given where a value belongs is refused with `:recognitum/not-a-value` by
  `check`, `recheck`, `seal`, `check-all`, `recheck-all`, `proven-checks`, `proven-concerns`,
  `clean` and `drafting`. `(rec/check T sel)` returned true before. `rec/proves?` still
  answers false.
- A draft opened before its type was redefined proves nothing: `rec/proves?` answers false
  for every selection.
- `rec/draft` of a value whose type name no longer names a definition of the type throws.
  It returned a draft before.

## 0.1.1 (2026-11-05)

- `defproven`, `defchecks`, `defcopy`, `defconcern` and `when-extant` carry `:style/indent`
  metadata, so CIDER and clojure-lsp indent them. The README shows the same rules for cljfmt.

## 0.1.0 (2026-11-05)

- First release.
