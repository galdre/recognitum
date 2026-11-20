# Testing a type and the code that uses it

The task: tests must show that a type accepts what it should and refuses what it should, and
tests of other code need valid values to work with. Some of the type's checks ask a database
or a service that a test cannot reach.

Three things make this short: a failure is data, so a test asserts which checks failed and not
what a message says; a check reads its source through a var, so a test can answer in the
source's place; and a probe asks the checks without building anything.

## The solution

A booking is valid where the room is free on each night. `room-free` is a **source**, a
function that check bodies read with `rec/fetch` or `rec/fetch-each`. In production it queries
a database; the stand-in below throws, as a database that a test cannot reach would.

```clojure
(ns hotel.booking
  (:require [clojure.test :as t :refer [deftest is]]
            [recognitum.core :as rec]))

(defn room-free
  "A source: for each key `[room night]`, whether the room is free on that night."
  [ks]
  (throw (ex-info "no database here" {})))

(rec/defproven Booking [guest room nights]
  rec/checks
  (guest  [] "the guest is named" (string? guest))
  (room   [] "the room is a positive number" (pos-int? room))
  (nights [] "the nights are a set of day numbers" (and (set? nights) (every? pos-int? nights)))

  (short-stay []
    "a booking has from 1 to 14 nights"
    (<= 1 (count nights) 14))
  (room-is-free [short-stay]
    "the room is free on every night"
    (every? true? (vals (rec/fetch-each room-free (map #(vector room %) nights))))))

;;; Helpers for the tests.

(defn free-except
  "A function to answer in the place of `room-free`: every room is free on every night, except
  the `[room night]` pairs in `taken`."
  [taken]
  (fn [ks] (zipmap ks (map #(not (contains? taken %)) ks))))

(defn failed-checks
  "The ids of the checks that fail when `f` is called, or nil where `f` returns."
  [f]
  (try (f) nil
       (catch clojure.lang.ExceptionInfo e
         (when (= :recognitum/check-failed (:error (ex-data e)))
           (set (keys (:failed (ex-data e))))))))

(def week {::guest "Ada" ::room 12 ::nights #{3 4 5}})

;;; The tests.

(deftest a-booking-of-a-free-room-is-made
  (with-redefs [room-free (free-except #{})]
    (is (rec/sealed? (map->Booking week)))))

(deftest a-booking-of-a-taken-room-is-refused
  (with-redefs [room-free (free-except #{[12 4]})]
    (is (= #{::room-is-free} (failed-checks #(map->Booking week))))))

(deftest a-stay-of-no-nights-is-refused-before-the-database-is-asked
  (is (= #{::short-stay} (failed-checks #(map->Booking (assoc week ::nights #{})))))
  (is (= #{::room-is-free} (:blocked (rec/probe Booking (assoc week ::nights #{}))))))

(deftest the-rules-that-need-no-database
  (is (true? (rec/probe Booking week rec/pure)))
  (is (= #{::guest} (set (keys (:failed (rec/probe Booking (assoc week ::guest nil) rec/pure)))))))

(deftest the-room-rule-with-an-answer-given-to-the-probe
  (is (true? (rec/probe Booking week rec/every {room-free (free-except #{})})))
  (is (= #{::room-is-free}
         (set (keys (:failed (rec/probe Booking week rec/every
                                        {room-free (free-except #{[12 5]})})))))))
```

At a REPL, `(t/run-tests)` runs them. The same call, with its printed output discarded:

```clojure
(select-keys (binding [t/*test-out* (java.io.StringWriter.)] (t/run-tests))
             [:test :fail :error])
;; => {:test 5 :fail 0 :error 0}
```

## Assert the data of a failure, not its message

A constructor, a write or a seal that fails throws an `ex-info`. Its data holds `:error`, and,
for a failed check, the report: `:failed` maps the id of each failed check to its failure, and
`:blocked` holds the ids of the checks that did not run. `failed-checks` above reads those. The
wording of a message is not promised, so a test that compares messages can break when a
docstring is reworded. [reference/failures.md](../reference/failures.md) states the data of
every throw.

Test the valid case of each check too. A check passes only where its body returns exactly
`true`, so a body that ends in `(seq nights)` or in `(some ...)` fails on valid data. The test
of a valid value finds that mistake, and no test of invalid values does.

## Answering in a source's place

A check body reads a source through the source's var, as it calls any function. There are two
ways to give a check another answer, and they differ in what the answer can reach:

- **`with-redefs` on the source's var.** The first two tests use it. The constructor runs under
  it, so the test gets a sealed value to work with. `with-redefs` replaces the var for every
  thread while it is in force, so it suits a test in which no other thread reads the source. A
  value that is made under it stays sealed afterward, and a draft that is checked under it
  remembers the pass. A test wants exactly that. Production code does not: there, a value
  would be proof of an answer that the real source never gave.
- **The fourth argument of `rec/probe` or `rec/probe-all`.** The last test uses it. It maps a
  source to a function that answers in the source's place, for that call only. A probe builds
  no instance of the type and remembers nothing, so this way tests the rules, and does not supply values to
  other tests.

`with-redefs` works in the same way on a function that a body calls, since a body calls it
through its var.

[reference/sources.md](../reference/sources.md) states both ways, and
[asking-without-building.md](asking-without-building.md) shows the second in production code.

## Testing the rules that need no source

`rec/pure` selects every check that reads no source. `(rec/probe Booking fields rec/pure)` runs
those checks and the checks that they wait on, so the fourth test needs no answer for
`room-free`. `rec/shape` selects only the shape checks, which are the checks named after
fields.

The third test shows a wait at work. `room-is-free` waits on `short-stay`, so a booking with no
nights fails `short-stay` alone, `room-is-free` is blocked, and the source is not asked. That
test passes though nothing answers for `room-free`.

## A test that forgot the source

A test that builds a value without answering for the source does not see the source's
exception thrown. The read fails its check, and the failure data holds the source's exception
under `:cause`:

```clojure
(failed-checks #(map->Booking week))
;; => #{::room-is-free}
(ex-message (:cause (get-in (rec/probe Booking week) [:failed ::room-is-free :data])))
;; => "no database here"
```

So where a check that reads a source fails in a test that was not written to test that check,
look first at whether the test answered for the source.

## Valid values for the tests of other code

Code under test that takes a `Booking` needs a sealed one. A function of the test namespace
makes it under `with-redefs`:

```clojure
(defn a-booking
  "A sealed Booking for a test: `week`, with `changes` merged in. Every room is free."
  [changes]
  (with-redefs [room-free (free-except #{})]
    (map->Booking (merge week changes))))

(rec/sealed? (a-booking {::room 7}))
;; => true
```

A later write to that value runs the checks that read a key it changes. A write of the room
runs `room-is-free`, which reads the source, so that write needs the answer again. A write of
the guest does not:

```clojure
(::guest (assoc (a-booking {}) ::guest "Grace"))
;; => "Grace"
(failed-checks #(assoc (a-booking {}) ::room 8))
;; => #{::room-is-free}
```

## A definition inside another form

A definition need not be a top-level form. It defines the same type inside a `let` or a `when`,
and where the whole form is expanded before it is evaluated, as `clojure.walk/macroexpand-all`
expands it. So a tool that wraps each top-level form in another form, as a coverage tool does,
or that expands the forms before it evaluates them, gets the same definition.

## Two more things to test

- **Every function with an effect refuses a value without proof.** [sinks.md](sinks.md) gives
  the test.
- **A test namespace that is reloaded.** A value that a test namespace holds in a `def` belongs
  to the definition of its type that was current when the `def` ran. After the type's form is
  evaluated again, that value is no longer sealed. [repl.md](repl.md) says what to do.
