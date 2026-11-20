# Guides

Each guide works through one task: it states the task, shows a whole solution as code that
runs, and then explains the choices. A reader who is new to the library starts with the
[tutorial](../tutorial.md), which the guides assume.

| Guide | The task |
|---|---|
| [Values built in steps, and values sealed together](drafts.md) | Build a sealed value from data that arrives in pieces or needs mending, and make several values or none. |
| [Checks that ask a database or a service](sources.md) | Write a check that reads an outside source, check a batch with one query, and ask again when the answer may have changed. |
| [Asking a type's checks about plain data](asking-without-building.md) | Report every mistake of a form at once, try an import before any row is written, and ask the checks with another answer from a source. |
| [One group of checks for several types](bundles.md) | Write the rules of an address once, use them in several types, twice in one type, and for an optional field. |
| [Values that are checked in parts](checked-in-parts.md) | Use a value while only some of its checks have passed, and let each user of it ask for the checks it needs. |
| [Functions that refuse a value without proof](sinks.md) | Make a function with an effect refuse an unproven value, and test that every such function does. |
| [Protocols and interfaces on a type](methods.md) | Give a type the methods of a protocol or a Java interface. |
| [Testing a type and the code that uses it](testing.md) | Assert which checks fail, answer in a source's place, and make valid values for other tests. |
| [Working at a REPL: when a type is defined again](repl.md) | Bring held values up to the new definition after a type's form is evaluated again. |

The [reference pages](../reference/README.md) state each rule in full, and
[The guarantee and its limits](../guarantee.md) states what holding a sealed value proves. The
[README](../../README.md) says what the library is and how to install it.
