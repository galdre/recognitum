# Changelog

## 0.3.0 (2026-11-12)

### Added

- `rec/probe` and `rec/probe-all` ask whether a map would make a valid value of a type, without
  making one. They answer what `rec/check` answers of a fresh draft holding the map's entries,
  `true` or a report, with the keys the type does not declare under `:undeclared`. They read
  any map (a plain map, a record, a draft or a value of any type) and remember nothing. An
  optional map of overrides answers in a source's place for that call only. `probe-all` runs
  over a batch of maps in one pass.
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
  no concern where it can tell: an unqualified symbol, or one whose namespace it has seen.
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
  and `:missing` holds the absent required fields. Code that matched
  `:recognitum/missing-fields` must match `:recognitum/check-failed` and read `:missing`.
- A run whose selection asks the presence of a field that a draft lacks answers a report, not
  `true`, even where every check it runs passes.
- `rec/proves?` answers false for every selection while a required field is absent.
- `rec/seal-all` reports a sealed value of a displaced definition at its path with
  `:recognitum/displaced`, and gives it back in `:drafts` as it is. Before, it returned such a
  value as it was.
- `rec/drafting-all` gives `f` a value of a displaced definition whose type's name names no
  definition as it is, and the seal reports it. Before, it threw
  `:recognitum/no-current-definition` before calling `f`.
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
