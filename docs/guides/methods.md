# Protocols and interfaces on a type

The task: a type should answer the methods of a protocol or of a Java interface, as a record
does, so that its values sort, print for people, or take part in the program's own protocols.

`rec/defproven` and `rec/defproven-in` take method sections after their checks, written as
`defrecord` writes them.

## The solution

A help desk's ticket describes itself, can be escalated, sorts by priority, and has a short
text for people.

```clojure
(ns help-desk.ticket
  (:require [recognitum.core :as rec]))

(defprotocol Describe
  (describe [ticket] "One line about the ticket.")
  (escalate [ticket] "The ticket, one step more urgent.")
  (archive [ticket] "The ticket, as the archive stores it."))

(rec/defproven Ticket [title priority ^:optional assignee]
  rec/checks
  (title    [] "the title is text" (string? title))
  (priority [] "the priority is 1, 2 or 3" (contains? #{1 2 3} priority))
  (assignee [] "the assignee is named" (string? assignee))

  Describe
  (describe [_]
    (str title " (priority " priority (when assignee (str ", with " assignee)) ")"))
  (escalate [this]
    (assoc this ::priority (max 1 (dec priority))))

  Comparable
  (compareTo [_ other] (compare priority (::priority other)))

  Object
  (toString [_] (str "#" priority " " title)))

(def printer (map->Ticket {::title "Printer on fire" ::priority 2}))
(def login (map->Ticket {::title "Cannot log in" ::priority 1 ::assignee "Ada"}))

(describe printer)
;; => "Printer on fire (priority 2)"
(describe login)
;; => "Cannot log in (priority 1, with Ada)"
(mapv ::title (sort [printer login]))
;; => ["Cannot log in" "Printer on fire"]
(str (escalate printer))
;; => "#1 Printer on fire"
(rec/sealed? (escalate printer))
;; => true
```

## Writing a method section

The checks sections come first: `rec/checks` and the bindings of bundles. The method sections
follow, each a protocol or an interface and then its methods, each `(method [this args...]
body...)`.

- **The first parameter is the value.** In `escalate` it is `this`. `recur` in a method body
  takes the method's other arguments, without the value, as in `defrecord`.
- **The fields are locals.** In a method body, the local of an absent optional field is `nil`:
  `describe` tests `assignee` with `when`. A check body differs: there, a read of an absent
  field fails the check. [reference/absence-and-nil.md](../reference/absence-and-nil.md) shows
  both.
- **A method changes a value by writing to it.** `escalate` calls `assoc` on `this`, and the
  write runs the checks that read the priority, so the method returns a sealed value or
  throws. A method body cannot call `map->Ticket` or `->Ticket`: such a method does not
  compile.
- **The type's name in a method body is the value's class.** `(instance? Ticket x)` works
  there. The name takes no type hint.

## What the values are

A sealed value is an instance of each interface that the type lists, and of the interface of
each protocol that it lists. So a protocol function, a direct call of the method, and Java
code that takes the interface all reach the type's method: above, `sort` called `compareTo`.

A **draft**, which is an unchecked map of a type, is not an instance of them, and a protocol
function throws for it. The drafts of every type have one class:

```clojure
(instance? Comparable printer)
;; => true
(instance? Comparable (rec/draft printer))
;; => false
(describe (rec/draft printer))
;; IllegalArgumentException: No implementation of method: :describe of protocol: #'help-desk.ticket/Describe found for class: recognitum.record.Draft
```

A value of a type that `rec/defproven-in` defined implements the type's protocols and
interfaces whatever checks it has passed. A method of such a type that relies on a check asks
`rec/proves?` first: [checked-in-parts.md](checked-in-parts.md).

## `toString`, `str` and printing

Of the methods of `Object`, a type may give only `toString`. `str` of a value is then that
text. Printing with `pr` or `prn` shows the tagged map whether or not the type gives
`toString`:

```clojure
(str login)
;; => "#1 Cannot log in"
(pr-str login)
;; => "#help-desk.ticket/Ticket #:help-desk.ticket{:title \"Cannot log in\", :priority 1, :assignee \"Ada\"}"
```

`equals` and `hashCode` are refused: a value's equality and hash are those of a map of its
entries.

## A method that the section leaves out

A section need not give every method of its protocol. A call of a method that it leaves out
throws `UnsupportedOperationException`. Above, `Ticket` gives no `archive`:

```clojure
(archive printer)
;; UnsupportedOperationException: no function implements archive
```

One kind of protocol method is an exception: a method that a map already has, with the same
name and the same number of arguments, such as `size` with no argument or `valAt` with one. A
section has to leave such a method out, because the definition refuses it, as the next section
says. A call of the protocol's function with a value of the type then does not reach a method
of the type: for `valAt` the map answers, and for `size` the call throws
`AbstractMethodError`. So a protocol that a type lists should not declare a method that a map
has.

## What a definition refuses

A value is also a map, and the definition refuses a method section that would clash with the
map. Each refusal leaves nothing defined, and its message says what to change. Among the
refusals:

- **A protocol method that a map already has**, such as `size` or `count` with no argument, or
  `valAt` with one. Rename the method, or extend the protocol to the type from outside the
  definition, as the next section describes.
- **An interface method that a map already has**, such as `count` of `clojure.lang.Counted`.
  Leave the method out, and the map's method answers.
- **`equals` and `hashCode`**, a method that the section's protocol or interface does not
  declare, and a method that more than one method of an interface matches. Type hints on the
  parameters choose among an interface's methods of one arity: `(tag [this ^String s] ...)`.
- **Interfaces that cannot be implemented together.** Four cases: two interfaces that give
  default bodies of one method, where the type does not give that method; two interfaces
  whose methods differ only in return type; `java.util.function.Predicate` or
  `java.util.function.BiConsumer`, which the library implements in a class of its own that it
  generates for the type; and an interface whose `print-method` entry Clojure prefers to a
  map's, since a value of the type could then not print as its map.
- **A checks section after a method section.**

The protocol below declares `size` with no argument, which a map has:

```clojure
(defprotocol Sized
  (size [x]))
```

A type that gives that method is refused:

```clojure
(rec/defproven Box [width]
  rec/checks
  (width [] (pos-int? width))

  Sized
  (size [_] width))
;; ExceptionInfo: help-desk.ticket/Box, line 6: method size of Sized: as a map, a value of Box already has a method size of 0 parameters, so the type cannot give it: rename it, or extend Sized to Box with extend-protocol after the definition (a method extended from outside is not guarded: it answers on values of a displaced definition)
```

The message names the line of the clause that is refused, as the Clojure reader counted it.
Here the form was evaluated alone, so line 6 is the sixth line of the form. Where a file is
loaded, it is the line of the file.

[reference/defproven.md](../reference/defproven.md#method-sections) lists everything that a
method section refuses. The list above gives a remedy for some of those refusals, and leaves out
the refusals of a section that is written wrongly, such as a method that is written twice.

## Extending a protocol from outside the definition

A protocol may be extended to the type with `extend-protocol` or `extend-type`, as to any
class. Two things differ from a method that the definition lists:

- The body gets the value as an argument and reads the fields from it. The fields are not
  locals there.
- The extension belongs to the class that it was made for. When the type is defined again, the
  values of the new definition do not answer the method until the protocol is extended again,
  and the values of the earlier definition still answer it.
  [reference/redefinition.md](../reference/redefinition.md) shows both.

```clojure
(defprotocol Urgent
  (urgent? [x]))

(extend-protocol Urgent
  Ticket
  (urgent? [ticket] (= 1 (::priority ticket))))

(mapv urgent? [printer login])
;; => [false true]
```

From another namespace, `extend-protocol` and a type hint name the class by its full name,
`help_desk.ticket.Ticket`, or by the name that an `:import` gives it. The namespace's alias
does not reach the class. [reference/names.md](../reference/names.md) shows the forms.
