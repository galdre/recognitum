# Changelog

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
