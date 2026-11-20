# Reference

The rules of one function are in its docstring: `(clojure.repl/doc recognitum.core/seal)`. The
docstring of the namespace `recognitum.core` lists every public function and macro. The pages
here hold the rules that span several functions. One page differs: the docstrings of
`rec/defproven` and `rec/defproven-in` state the form and what is thrown, and
[defproven.md](defproven.md) states the rest of the form's rules. Each page stands alone.

| Page | Answers |
|---|---|
| [The definition form](defproven.md) | What do `rec/defproven` and `rec/defproven-in` take: fields, checks sections, a clause, waits, flags, a bundle's binding, method sections? What does a definition refuse, and what does a refused definition leave? |
| [When a check runs](when-checks-run.md) | Which checks does each call run, `rec/check-all`, `rec/recheck-all` and `rec/seal-all` among them? What happens when a check that another waits on fails? How do I run the benchmark? |
| [Absent fields and nil](absence-and-nil.md) | What is the difference between an absent field and a field that holds `nil`? What does each function do where a required field is absent? Where may `rec/extant?` and `rec/when-extant` be written? |
| [How a write is checked](writes.md) | Which checks does `assoc` run? Is a write of several keys one write? What happens to a key the type does not declare? |
| [What drafts and values of a `rec/defproven-in` type remember](memory.md) | What makes a draft forget a check, and what does not? What does a draft prove while it holds a key the type does not declare? When do I need `rec/recheck`? |
| [Sources and how they are called](sources.md) | What must a source accept and return? How many times is it called for a batch? Where may a read be written? How do I answer in its place? |
| [Selections](selections.md) | What does each selection select? What does a keyword mean? What happens when a selection selects nothing in a type? What does `rec/proves?` answer for a value, a draft and anything else, and when does it throw? |
| [Failures](failures.md) | What is in a report, and in the data of a throw? What does `rec/seal-all` throw for the drafts that fail? Which `:error` keywords exist? |
| [Redefinition](redefinition.md) | What happens to the values, drafts and constructors I hold when a type is defined again? |
| [Printing, reading, equality and metadata](printing-and-reading.md) | How does a value of a type print and read back? Does it equal a plain map? Does it keep metadata? |
| [What a definition names](names.md) | Which class, vars and keywords does a definition make, and how does another namespace write them? How does a type compare with a record? |
| [Editor support](editor-support.md) | What does the clj-kondo configuration report and miss? How do I set up indentation? |

[The guarantee and its limits](../guarantee.md) states what holding a sealed value proves, and
what it does not. The [guides](../guides/README.md) each work through one task, with code that runs.
The [README](../../README.md) says what the library is and how to install it.

## Stability

Before 1.0, `recognitum.core` may change between minor versions; the [changelog](../../CHANGELOG.md) lists every
breaking change. The layers below it are unstable and may change in any release.
[Internals](../internals.md) describes those layers, for a reader who calls them directly or who
changes the library.
