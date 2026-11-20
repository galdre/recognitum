# Editor support: linting and indentation

The library ships a clj-kondo configuration, which clj-kondo and clojure-lsp use to read the
defining macros, and the macros carry indentation metadata. Neither changes what the macros
accept: the macros themselves are the authority on a definition, and they refuse a wrong one
when its namespace loads.

## Importing the lint configuration

The configuration is on the classpath, under `clj-kondo.exports/recognitum/recognitum`. To copy
it into a project, make the project's `.clj-kondo` directory and run:

```text
clj-kondo --lint "$(clojure -Spath)" --copy-configs --skip-lint
```

clj-kondo 2026.10.20 reads the copied configuration as it stands: the project's
`.clj-kondo/config.edn` needs no entry for it.

## What the lint reports

The configuration teaches clj-kondo and clojure-lsp the definition forms. It lints method
bodies as clj-kondo lints the method bodies of a `defrecord`. Its own findings carry linter
names that begin with `:recognitum/`.

It reports most of the mistakes that the macros refuse:

- a misspelled wait, concern, input or field;
- a read (`rec/fetch`, `rec/fetch-each`) outside a check body, or inside a function that the
  body builds;
- one of the names that the library reserves for its own reads, such as `&field` and `&fetch`,
  written in a check body;
- a `rec/defcopy` map that does not name every check of the bundle;
- a bundle bound twice in one type;
- waits that form a cycle;
- a checks section after a protocol.

It always reports these three:

- a flag written outside the place of a clause's flags, where the flag is a keyword or a
  concern that the lint knows;
- a check whose whole body is a concern that the lint knows;
- `::name` where the `ns` form refers `name` from another namespace.

## What the lint does not report

- **It reports nothing in a definition that the macros accept.**
- **It may miss a mistake that the macros refuse.** A definition that lints clean can still be
  refused when its namespace loads.
- **Cycles through check bodies.** The lint reports the cycles of the waits that the forms
  list, and of the fields that bindings name in `:when-extant`. It does not read check bodies,
  so only the macros report a cycle through a field that a body reads.
- **Cycles through another namespace.** The lint sees one form at a time, so only the macros
  report a cycle through the waits of a bundle that another namespace defines.

## Docstrings of copied checks

Under clj-kondo's `:missing-docstring` linter, a check that `rec/defcopy` copied from a
documented check is not reported. Where the bundle is defined in another file, an editor may
show the copy without its docstring. At run time, `(doc ...)` shows the docstring.

## Indentation

The macros carry `:style/indent` metadata, which CIDER and clojure-lsp read. `clojure-lsp format`
reads it when it is run with `--analysis '{:type :project-and-shallow-analysis}'`.

- `rec/defproven` and `rec/defproven-in` indent as `defrecord` does.
- `rec/defchecks`, `rec/defcopy` and `rec/defcontext` indent as `defn` does.
- `rec/defconcern` and `rec/when-extant` indent as `when` does.

With cljfmt alone, or with Calva's formatter, add the same rules to the project's
`.cljfmt.edn`:

```text
{:extra-indents {recognitum.core/defproven    [[:block 2] [:inner 1]]
                 recognitum.core/defproven-in [[:block 2] [:inner 1]]
                 recognitum.core/defchecks    [[:inner 0] [:inner 1]]
                 recognitum.core/defcopy      [[:inner 0]]
                 recognitum.core/defconcern   [[:block 1]]
                 recognitum.core/defcontext   [[:inner 0]]
                 recognitum.core/when-extant  [[:block 1]]}}
```
