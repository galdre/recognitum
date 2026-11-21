(ns recognitum.core
  "Types whose values carry proof that their checks passed.

  [[defproven]] defines a type from its fields and named checks. Its constructors run every
  check or throw, and every write to one of its values runs the checks that read a key the
  write changes, or throws. So a value of the type is **sealed**: holding one is holding proof
  that the checks passed. [[sealed?]] is the whole test, and `instance?` gives the same answer
  until the type is redefined. A **draft** is an unchecked map of a type, for values built in
  steps; [[seal]] checks it and returns a sealed value.

  [[defproven-in]] defines a type whose values are made and written without checks, and carry
  in place the checks that passed on them: proof is asked with [[proves?]], never `instance?`.
  A check that needs a held value's proof asks [[proves?]] too, since a [[defproven-in]] value
  is an instance of its type's class without having passed its checks.

  The vocabulary:

  - A **check** is a named body that passes by returning exactly `true`; anything else it
    returns is its failure data. Its id is a keyword in the namespace that defines it. A check
    named after a field is that field's **shape check**.
  - A check **waits** on the checks it names and on the shape check of each field it reads,
    and runs only once they have passed.
  - A **bundle** ([[defchecks]]) is a group of checks over named inputs, bound into a type by
    saying which field each input reads. [[defcopy]] copies one under new names.
  - A **concern** ([[defconcern]]) marks checks so that a selection can select them together.
  - A **selection** selects some of a type's checks: a check id, a concern, a bundle, a bundle's
    check, or [[every]], [[shape]], [[pure]], [[fetching]], [[reading]], [[except]] and
    [[union]].
  - A **source** is a function from a vector of distinct keys to a map from key to answer.
    Check bodies read one with [[fetch]] and [[fetch-each]].
  - A field not marked `^:optional` is **required**. Its presence is a check of its own, with
    no name, part of the field's shape: a selection selects it as it selects a shape check that
    reads only that field and no source, a seal fails where the field is absent, and
    [[proves?]] is false while the field is absent. Every check that reads the field waits on
    its presence check, and this one wait never keeps a check from running.

  The public API:

  - Define: [[defproven]], [[defproven-in]], [[defchecks]], [[defcopy]], [[defconcern]],
    [[defcontext]], [[checks]].
  - Inside a check body: [[fetch]], [[fetch-each]], [[extant?]], [[when-extant]].
  - Select: [[every]], [[shape]], [[pure]], [[fetching]], [[reading]], [[except]], [[union]].
  - Build values: `map->T`, `->T` and the tagged literal `#ns/T {...}`, each generated per
    type; [[draft]], [[clean]], [[seal]], [[seal-all]], [[drafting]], [[drafting-all]].
  - Run checks: [[check]], [[recheck]], [[check-all]], [[recheck-all]].
  - Ask of plain data: [[probe]], [[probe-all]].
  - Ask: [[proves?]], [[proven-checks]], [[proven-concerns]], [[checks-of]], [[selects-nothing?]],
    [[sealed?]], [[draft?]], [[data-readers]]."
  (:require
   [recognitum.body :as body]
   [recognitum.define :as define]
   [recognitum.define.bundles :as bundles]
   [recognitum.engine :as engine]
   [recognitum.engine.runner :as runner]
   [recognitum.engine.waves :as waves]
   [recognitum.proof.key-class :as key-class]
   [recognitum.record.draft :as draft]
   [recognitum.record.probe :as probe]
   [recognitum.record.runs :as runs]
   [recognitum.record.types :as types]
   [recognitum.record.values :as values]
   [recognitum.record.walk :as walk]
   [recognitum.select :as select]))

(def checks
  "Starts the section of a definition that holds its own checks."
  ::checks)

(def ^:private strategy
  "The proof strategy every type is defined with."
  key-class/strategy)

(def ^:private wiring
  {:strategy strategy :define #'engine/define :run-all #'waves/run-all :runner #'runner/runner})

(def ^:private expansion
  "What the defining macros pass to `recognitum.define` and `recognitum.define.bundles` when they
  expand:

  - `:compile-body`, the engine's compiler of a check body;
  - `:read-macros`, a map from the symbol of each body macro's var to the kind of read it is;
  - `:checks-marker`, the symbol of the var that starts a section of own checks;
  - `:strategy`, the proof strategy, which answers the name of a type's class and refuses a
    definition that it cannot make."
  {:compile-body engine/body-form
   :read-macros `{fetch :fetch, fetch-each :fetch-each, extant? :extant?, when-extant :when-extant}
   :checks-marker `checks
   :strategy strategy})

;;; ------------------------------------------------------------------ definitions

(defmacro defproven
  "Defines the type `T`: its class, imported into this namespace, and the constructors `map->T`
  and `->T`, which run every check and return a sealed value or throw.

      (rec/defproven Heist [name crew take cuts ^:optional getaway]
        rec/checks
        (name [] (non-blank? name))
        (cuts-sum-to-take [] (= take (reduce + (vals cuts))))
        (only-crew-get-cuts [cuts-sum-to-take] (every? crew (keys cuts))))

  The form is `(rec/defproven T [fields*] checks-sections* method-sections*)`:

  - A field's key is the keyword in this namespace named after it, as `::take`. A field marked
    `^:optional` may be absent; every other field must be present, and a field that holds nil
    is present. `map->T` takes a map from field keys to values; `->T` takes every field, in
    order.
  - A checks section is `rec/checks`, at most once, then the type's own clauses; or a bundle
    var, then one `(input [] body)` clause per input of the bundle. An input clause's body is
    an expression of the fields, and the definition is refused where that body reads a
    source. `^{:when-extant field}` on the bundle var skips that bundle's checks, as passing,
    while `field` is absent; the definition is refused unless `field` is an optional field.
  - A method section is a protocol or an interface, then its methods, each
    `(method [this args*] body*)`, as in `defrecord`. The method sections follow the checks
    sections. In a method body the fields are locals, nil where absent.

  An own clause is `(name [waits] flags? \"doc\"? body...)`. It defines the check whose id is
  `::name`:

  - In the body the fields are locals. The check passes when the body returns exactly `true`;
    anything else the body returns, truthy or not, is the check's failure data. A read of an
    absent field fails the check with the failure data `{:absent key}`, where `key` is the
    field's key; [[extant?]] and [[when-extant]] ask whether a field is present without
    reading it.
  - A check named after a field is that field's shape check. The shape check of an optional
    field passes where the field is absent.
  - A check runs only once every check it waits on has passed. Every check waits on the shape
    check of each field its body reads, so `waits` need name only the other checks: an own
    check by its bare name; a bundle's check, or every check of a bundle, by the qualified
    var, `bundle-ns/check` or `bundle-ns/bundle`, even where the bundle is defined in this
    namespace.
  - `flags` holds the concerns the check carries, and `:override` where the clause replaces a
    check. A concern is written as the symbol of the var [[defconcern]] defined, or as the
    concern's id. A clause named `bundle-ns/check` whose flags hold `:override` replaces that
    check of a bound bundle. The flags go right after the waits, before the docstring, and
    several go in one set: `(c [waits] #{concern ::other} \"doc\" body)`. A flag written
    later in the clause, before the body's last form, is refused.

  A write to a sealed value (`assoc`, `dissoc`, `conj`, `merge`, `into`) runs the checks that
  read a key the write changes, and returns a new value or throws. A constructor or a write
  that fails throws ex-info: `:error` is `:recognitum/undeclared-keys` for a key the type does
  not declare, or `:recognitum/check-failed` where a check fails or a required field is absent. A
  definition that is refused throws ex-info whose `:error` is `:recognitum/refused`, and
  defines nothing. Evaluating the form again redefines `T`, and the values of the earlier
  definition are no longer sealed.

  `docs/reference/defproven.md` states the rest: every refusal, the rules of a check body, of a
  bundle's binding and of the method sections, and what a failed definition leaves.
  `docs/reference/redefinition.md` states the rules of redefinition."
  {:arglists '([T [fields*] sections* method-sections*])
   :style/indent [2 nil nil [:defn]]}
  [tname fields & sections]
  (define/defproven &env tname fields sections
    (assoc expansion :wiring `@(var wiring))))

(defmacro defproven-in
  "Defines the type `T` from the form [[defproven]] takes. Nothing runs the type's checks but a
  call that asks to run them: `map->T`, `->T` and the tagged literal check nothing, and a write
  (`assoc`, `dissoc`, `merge`, `conj`, `into`) checks nothing. A value of the type may therefore
  lack a required field. A constructor or a write given a key the type does not declare still
  throws ex-info whose `:error` is `:recognitum/undeclared-keys`.

      (rec/defproven-in Ballot [choice ^:optional round]
        rec/checks
        (choice [] (string? choice))
        (round-positive [] (rec/when-extant round (pos? round))))

  A value of the type carries, in place, the checks that passed on its entries. [[check]],
  [[recheck]], [[check-all]], [[recheck-all]], [[seal]] and [[seal-all]] run checks on a value,
  and the value remembers what passed and forgets what failed; every holder of the value sees
  what the value remembers. A write returns a new value remembering what the old one passed,
  less the checks that read a key the write changes.

  A value of the type is never sealed: [[sealed?]] answers false, and code that needs proof asks
  [[proves?]]. Every value implements the type's protocols and interfaces, whatever it has
  passed. The type has no drafts: [[draft]] given its class, and [[draft]], [[clean]] and
  [[drafting]] given one of its values, throw ex-info whose `:error` is
  `:recognitum/no-drafts`. [[seal-all]] enters a value as it enters a draft, and
  [[drafting-all]] leaves it as it is.

  Evaluating the form again redefines `T`, and a value of the earlier definition reads as
  before and proves nothing. `docs/reference/redefinition.md` states what such a value
  refuses, and `docs/reference/defproven.md` states the form in full."
  {:arglists '([T [fields*] sections* method-sections*])
   :style/indent [2 nil nil [:defn]]}
  [tname fields & sections]
  (define/defproven &env tname fields sections
    (assoc expansion :wiring `@(var wiring) :unsealed true)))

(defmacro defchecks
  "Defines a bundle: a var holding checks over `inputs`, with the docstring `doc-string` if one
  is given, and one var per check.

      (rec/defchecks cast-into-box
        \"The checks of a cast into a ballot box.\"
        [voter ballot-box-id]
        rec/checks
        (box-exists [] (some? (rec/fetch db/ballot-boxes ballot-box-id)))
        (may-cast [box-exists] (db/can-cast? voter ballot-box-id)))

  A clause is written as an own clause of [[defproven]] is, with the inputs in place of the
  fields: in a body the inputs are locals, and [[extant?]] and [[when-extant]] take an input.
  A clause's name is a plain symbol, its waits name only checks of this bundle, by their bare
  names, and no clause takes `:override`. Each check's id is a keyword in this namespace.

  A type binds the bundle with one clause per input, as [[defproven]] describes. Every input
  may be absent in such a type: a read of an absent input fails the check with the failure
  data `{:absent :input}`, where `:input` is the input's name as a keyword."
  {:arglists '([name doc-string? [inputs*] rec/checks clauses*])
   :style/indent [:defn [:defn]]}
  [bname & args]
  (let [[doc inputs marker & clauses] (if (string? (first args)) args (cons nil args))]
    (bundles/defchecks &env bname doc inputs marker clauses expansion)))

(defmacro defcopy
  "Defines `new-name`, a copy of `bundle` whose checks are renamed by `names`, a map from each
  check of the bundle to its new name, which names every check exactly once. The copy's var has
  the docstring `doc-string` if one is given, and each renamed check gets a var, as under
  [[defchecks]]. The copy's ids are keywords in this namespace; its checks keep their concerns
  and their docstrings."
  {:arglists '([new-name doc-string? bundle names])
   :style/indent :defn}
  [new-name & args]
  (bundles/defcopy new-name args))

(defmacro defcontext
  "Defines `name` as a context: a var holding the selection `sel`, with the docstring `doc`. A
  context means nothing beyond its selection: every function that takes a selection answers
  for the context as it answers for `sel`."
  {:style/indent :defn}
  [name doc sel]
  `(def ~(vary-meta name assoc :doc doc) ~sel))

(defmacro defconcern
  "Defines the concern `name`, a var with the docstring `doc`. A concern marks checks so that
  a selection can select them together. A check carries the concern where its clause has
  `name` or the concern's id among its flags, right after its waits, as [[defproven]]
  describes: `(c [waits] name body)`. The concern, which is the var's value, and its id are
  each a selection of the checks that carry it.

  The id is `::name` in this namespace. In a namespace that refers the concern, `::name` is
  no concern's id, and a clause that writes it as a flag or as a check's whole body is
  refused; that namespace writes `name` or the id in full."
  {:style/indent 1}
  [name doc]
  (bundles/defconcern name doc))

;;; ------------------------------------------------------------------ check bodies

(defn- outside! [form what]
  (throw (IllegalStateException.
          (str what " can be used only inside a check body of rec/defproven or rec/defchecks: "
               (pr-str form)))))

(defmacro fetch
  "Inside a check body only: reads `k` from `source` and returns its answer, or nil where the
  source leaves `k` out. A source is a function from a vector of distinct keys to a map from
  key to answer; one call of it can carry the keys that several checks and values read in one
  pass. A read asks its source only when the body reaches it.

  A source that throws an `Exception` fails the check with the failure data `{:fetch-failed
  source :cause e}`, where `e` is what the source threw; where `e` is an
  `InterruptedException`, the read restores the calling thread's interrupt flag. An answer
  that is a `Throwable` fails the reads of its key in the same way, as the `:cause`. An
  `Error` from a source propagates out of the call that ran the check.

  Legal only in call position and outside any fn the body builds (fn, #(...), for, lazy-seq,
  delay) and outside `locking`. Throws at expansion anywhere else, and in an input clause of
  a bundle's binding."
  [source k]
  (when-not (contains? &env body/marker) (outside! &form "rec/fetch"))
  (list '&fetch source k))

(defmacro fetch-each
  "Inside a check body only: reads every key of `ks` from `source` in one read, and returns a
  map from key to answer. The rules of [[fetch]] apply."
  [source ks]
  (when-not (contains? &env body/marker) (outside! &form "rec/fetch-each"))
  (list '&fetch-each source ks))

(defmacro extant?
  "Inside a check body or an input clause of a bundle's binding only: whether the field `f` is
  present; a field that holds nil is present. In a body of [[defchecks]], `f` is an input. A
  check that asks waits on the field's shape check, as a check that reads the field does.

  Legal only in call position. Unlike [[fetch]], legal inside a fn the body builds (fn,
  #(...), for, lazy-seq, delay) and inside `locking`. Throws at expansion anywhere else."
  [f]
  (when-not (contains? &env body/marker) (outside! &form "rec/extant?"))
  (list '&extant? f))

(defmacro when-extant
  "Inside a check body or an input clause of a bundle's binding only:
  `(if (rec/extant? f) (do body...) true)`. Legal wherever [[extant?]] is."
  {:style/indent 1}
  [f & body]
  (when-not (contains? &env body/marker) (outside! &form "rec/when-extant"))
  `(if (extant? ~f) (do ~@body) true))

;;; ------------------------------------------------------------------ selections

(def every "Selects every check." select/every)
(def shape "Selects every shape check." select/shape)
(def pure "Selects every check that reads no source." select/pure)

(defn fetching
  "Selects the checks that read `source`."
  [source]
  (select/fetching source))

(defn reading
  "Selects the checks that read the field whose key is `k`, directly or through an input."
  [k]
  (select/reading k))

(defn except
  "Selects what `s` selects, less what any of `xs` selects. Throws ex-info whose `:error` is
  `:recognitum/unknown-name` where a keyword among them names no concern, no bundle check and
  no check of a type its namespace defines."
  [s & xs]
  (types/refuse-unnamed! (apply select/except s xs)))

(defn union
  "Selects what any of `xs` selects; `(union)` selects nothing. Throws ex-info whose `:error`
  is `:recognitum/unknown-name` where a keyword among them names no concern, no bundle check
  and no check of a type its namespace defines."
  [& xs]
  (types/refuse-unnamed! (apply select/union xs)))

;;; ------------------------------------------------------------------ values

(defn draft
  "A draft of a [[defproven]] type: a map that accepts any write, a key the type does not
  declare included, and remembers which checks pass on its entries. A write returns a new
  draft that forgets the checks that read a key it writes. [[seal]] checks a draft and
  returns a sealed value. A draft does not equal a plain map of its entries. It prints as
  `#recognitum/draft [ns/T {...}]`, which no reader reads.

  - Given a type's class, a draft holding nothing and passing nothing.
  - Given a sealed value, a draft holding its entries and passing every check.
  - Given a draft, that draft.
  - Given a value of a displaced definition, one that a later definition of its type
    replaced, a draft of the current definition holding its entries and passing nothing.
    Where the type's name no longer names a definition of the type, throws ex-info whose
    `:error` is `:recognitum/no-current-definition`.

  While a draft holds a key its type does not declare, [[proves?]] of it is false, whatever it
  remembers; what it remembers is kept, and once [[clean]] or `dissoc` removes the key,
  [[proves?]] again answers by what the draft remembers.

  Throws ex-info whose `:error` is `:recognitum/no-drafts` given the class or a value of a
  [[defproven-in]] type, and `:recognitum/not-a-type` given anything else."
  [x]
  (values/draft x))

(defn clean
  "Draft `d` without the keys its type does not declare, remembering what `d` remembers.
  Throws ex-info whose `:error` is `:recognitum/not-a-draft` given a sealed value, and
  `:recognitum/no-drafts` given a value of a [[defproven-in]] type."
  [d]
  (values/clean d))

(defn seal
  "The sealed value made from draft `d`, once every check `d` does not remember as passing has
  passed; a sealed value is returned as it is. A failed seal leaves `d` remembering
  the checks that passed, so the next seal runs only the rest.

  With `sel`, a sealed value reads `sel` as [[proves?]] does, and throws as [[proves?]] does
  where `sel` is no selection or holds an unknown name.

  A seal that fails throws ex-info whose data holds the type's name under `:type` and, under
  `:error`:

  - `:recognitum/undeclared-keys`, before any check runs, where `d` holds a key its type does
    not declare, with those keys under `:keys`; or
  - `:recognitum/check-failed`, where a check fails or a required field is absent, with the
    report of [[check]] under `:failed` and `:blocked`, and under `:missing` the required
    fields `d` lacks where it lacks any. The seal runs its checks whatever is absent, so one
    failure names both; `:failed` is empty where only fields are absent.

  With `sel`: a draft seals against every check, so `sel` is [[every]] or the seal throws
  ex-info whose `:error` is `:recognitum/draft-selection`, running nothing. A value of a
  [[defproven-in]] type runs the checks `sel` selects, what they wait on and the shape check of
  each field it must or does hold, less what it passed, and is returned itself, remembering
  what passed; or the seal throws as above. Where `sel` is not [[every]] and selects nothing in
  the value's type (see [[selects-nothing?]]), the seal throws ex-info whose `:error` is
  `:recognitum/selects-nothing` before any check runs, the shape checks included, whatever the
  value holds or has passed: such a seal would prove nothing. A type with nothing to prove for
  a concern says so with a check that carries the concern and passes. After a seal that
  returns, `(proves? v sel)` is true. Without `sel`, it is sealed against [[every]], which is
  never refused for selecting nothing.

  Before any check runs, the seal also throws ex-info whose `:error` is
  `:recognitum/displaced-constructor` given a draft of a displaced definition, one that a later
  definition of its type replaced; `:recognitum/displaced` given a value of a displaced
  definition, with the message a write to that value gives, which names the type and the way
  to a value of the current definition, `(rec/seal (rec/draft v))` for a value of a
  [[defproven]] type and `(ns/map->T (into {} v))` for a value of a [[defproven-in]] type;
  `:recognitum/not-a-value` given a type's class; and `:recognitum/not-a-draft` given anything
  else."
  ([d]
   (values/seal d))
  ([d sel]
   (values/seal d sel)))

(defn check
  "Runs the checks `sel` selects in `x`, and those they wait on, that `x` does not already pass.
  A draft, or a value of a [[defproven-in]] type, remembers what passed and forgets what
  failed. A key that a draft holds and its type does not declare is not checked: the answer
  can be true where [[seal]] would throw for that key, and [[proves?]] is false while the draft
  holds it. A sealed value runs nothing and answers true. True from `check` is therefore no
  proof; [[sealed?]] and [[proves?]] answer whether a value proves its checks.

  Returns true, or a report: `{:failed {id {:data :doc :blocked}} :blocked #{id}}`. Under a
  failed check, `:data` is its failure data, `:doc` its docstring where it has one, and
  `:blocked` the checks its failure kept from running. `:pulled-back` explains each failed
  check that an [[except]] removed and a wait ran anyway.

  A selection asks the presence of a required field where it selects the field's presence check
  or a check that waits on that presence check, directly or through other checks; every check
  waits on the presence check of each required field it reads. Where `x` is a draft or a value
  of a [[defproven-in]] type and lacks a field whose presence `sel` asks, the answer is a
  report, never true, and holds each such field under `:missing`. A presence check is selected as
  a shape check that reads only its field and no source would be: [[every]], [[shape]] and
  [[pure]] select every required field's; `(reading k)` selects that of the field whose key is
  `k`; [[union]] selects what any part selects; [[except]] selects what its first part selects
  less what each later part selects; any other selection, a check id or a concern among them,
  selects none. The wait of a check on a presence check never keeps the check from running.

  Throws ex-info whose `:error` is `:recognitum/unknown-name` where `sel` is or holds a keyword
  that names no check of the type of `x`, no concern and no bundle check;
  `:recognitum/not-a-selection` where `sel` is no selection; `:recognitum/not-a-type` where `x`
  is of no type; and `:recognitum/not-a-value` where `x` is a type's class. Given a class,
  [[recheck]] and [[seal]] throw `:recognitum/not-a-value` too, as do [[check-all]] and
  [[recheck-all]] where `xs` holds one; [[proves?]] answers false.

  Where `x` is of a displaced definition, one that a later definition of its type replaced,
  `check` throws, before any check runs, what [[seal]] throws for `x`: `:recognitum/displaced`
  for a value, with the message a write to that value gives, and
  `:recognitum/displaced-constructor` for a draft."
  [x sel]
  (runs/check x sel))

(defn recheck
  "Runs the checks `sel` selects in `x` whether or not `x` passes them, and those they wait on
  that it does not. A draft, or a value of a [[defproven-in]] type, remembers as under
  [[check]]; a sealed value stays as it is, whatever the checks answer. Returns and throws as
  [[check]] does."
  [x sel]
  (runs/recheck x sel))

(defn check-all
  "Runs what [[check]] would run on each value of `xs`, which may be of several types, in one
  pass, so values that read the same source share its calls. Each draft, and each value of a
  [[defproven-in]] type, remembers what passed and forgets what failed, as under [[check]].
  Returns a vector of what [[check]] returns, one per value, in order. Throws as [[check]] does;
  where `xs` holds a value or a draft of a displaced definition, it throws what [[check]] throws
  for that one before any check of any value in `xs` runs."
  [xs sel]
  (runs/check-all xs sel))

(defn recheck-all
  "Runs what [[recheck]] would run on each value of `xs`, which may be of several types, in one
  pass, so values that read the same source share its calls. Each draft and each value of a
  [[defproven-in]] type remembers as under [[recheck]]; a sealed value stays as it is. Returns a
  vector of what [[recheck]] returns, one per value, in order, and throws as [[check-all]]
  does."
  [xs sel]
  (runs/recheck-all xs sel))

(defn seal-all
  "Seals every draft in `shape`, a value of plain data, all or nothing, and returns `shape`
  as the walk below rebuilds it, with each draft replaced by its sealed value. A value of a
  [[defproven-in]] type is sealed in place against `sel` (against [[every]] without one), as
  [[seal]] seals it; drafts are sealed against every check, whatever `sel` is.

  The walk enters these, and nothing else: a map, keys and values, as `clojure.walk` enters
  it, a record included; a map entry; a vector; a list; a set; a queue (a
  `clojure.lang.PersistentQueue`); any other sequence, a lazy one included; and the fields of
  every draft. A map, a record, a map entry, a vector, a list and a set each come back as a
  collection of the same kind, and a sorted map or set comes back sorted as it was. A queue
  comes back as a vector, and so does any other sequence, whether or not it holds a draft, in
  what is returned and in `:drafts`. A sealed value is not entered and comes back as it is.

  Anything else is not searched and comes back as it is, and a draft inside it stays a draft
  that no check ran on: a Java collection such as an `ArrayList` or a `HashMap`, an array, a
  reference such as an atom, a transient, an object of a `deftype`. Seal a draft before
  putting it in one of these, or give `seal-all` the drafts in a vector.

  Inner drafts are sealed first: a draft holding drafts is checked holding their sealed values, or,
  where one failed, that draft. Each draft is checked as [[seal]] would check it, even where a
  draft it holds failed, and remembers what [[seal]] would leave it remembering. The drafts at
  one level, counted from the innermost, are checked in one pass, as [[check-all]] checks
  them, so they share each source's calls.

  Where a draft does not seal, throws one ex-info whose data holds `:error`
  `:recognitum/drafts-failed`; `:failures`, a map from the path of each draft that failed to
  the ex-data [[seal]] would have thrown for it; and `:drafts`, `shape` as walked with every
  draft in place, ready to mend at those paths and seal again. A path is what `get-in` takes,
  with an index for a list, a queue or a sequence and a set's member for a set; a draft in key
  position ends its path with `:recognitum.core/key` after the key. A check body that throws
  makes `seal-all` throw it.

  The walk enters a [[defproven-in]] value's fields as a draft's, sealing what they hold first.
  It comes back as the very value given unless the walk replaced a draft in it; then it comes
  back as a new value, each field holding such a draft written as `assoc` writes it, so it
  forgets the checks that read those fields, and is sealed. In `:drafts`, such a value holds
  each draft back in its field. A [[defproven-in]] value in whose type `sel`, not [[every]],
  selects nothing fails at its path with the error `:recognitum/selects-nothing`, as [[seal]]
  refuses it, and none of its checks runs; the walk still seals what it holds. Drafts and
  sealed values are never refused for their selection.

  A value of a displaced definition, one that a later definition of its type replaced, proves
  nothing, whether [[defproven]] or [[defproven-in]] defined the type: it fails at its path
  with the error `:recognitum/displaced`, beside every other failure, whether or not its
  type's name names a current definition, and is given back in `:drafts` as it is."
  ([shape]
   (walk/seal-all shape ::key))
  ([shape sel]
   (walk/seal-all shape sel ::key)))

(defn drafting-all
  "[[seal-all]] of `(f opened)`, where `opened` is `shape` walked as [[seal-all]] walks it,
  with each sealed value it reaches opened as a draft and each draft left as it is, neither
  entered. `f` may return a different shape. Throws as [[seal-all]] does. A value of a
  [[defproven-in]] type is neither opened, nor entered, nor sealed, as a string is not: it
  comes back as `f` left it, a draft inside it unsealed. A value of a displaced
  definition of a [[defproven]] type is opened as [[draft]] opens it, as a draft of the current
  definition; where its type's name names no current definition, it is left as it is, `f`
  gets it, and the seal reports it as [[seal-all]] does.

  What [[seal-all]] does not search, `drafting-all` does not search: a sealed value inside a
  Java collection, an array, an atom or an object of a `deftype` is not opened, and `f` gets
  the holder as it is."
  [shape f]
  (walk/drafting-all shape f ::key))

(defn drafting
  "Given a sealed value, `(seal (f (draft v)))`. Given a draft, `(f v)`, unsealed: `drafting`
  seals only what it opened, so inside [[drafting-all]]'s `f` it leaves the opened drafts to
  [[drafting-all]]'s seal."
  [v f]
  (walk/drafting v f))

(defn proves?
  "Whether `x` holds every required field and passes the checks `sel` selects, those they wait
  on, and the shape check of each field it must or does hold. Runs nothing.

  Given a sealed value, a draft or a value of a [[defproven-in]] type, each of a type's current
  definition, `proves?` reads `sel` first: it throws ex-info whose `:error` is
  `:recognitum/unknown-name` where `sel` is or holds a keyword that names no check of the type,
  no concern and no bundle check, a check id of another type included, and
  `:recognitum/not-a-selection` where `sel` is no selection. Then it is true for the sealed
  value, also where `sel` is a concern no check of its type carries, or a bundle the type does
  not bind. For the draft it is false while the draft holds a key its type does not declare,
  else a matter of what it holds and remembers. For the value of a [[defproven-in]] type it is
  a matter of what it remembers, and false where `sel` is not [[every]] and selects nothing in
  its type (see [[selects-nothing?]]), whatever it has passed, as [[seal]] by `sel` refuses it.

  False, with `sel` unread, for a value or a draft of a displaced definition, one that a later
  definition of its type replaced, for a type's class, and for anything of no type."
  [x sel]
  (values/proves? x sel))

(defn probe-all
  "For each map of `field-maps`, whether it would make a valid value of the type whose class is
  `T` under the checks `sel` selects ([[every]] where none is given): what [[check]] with `sel`
  answers of a fresh draft of `T` holding the map's entries, true or a report, with the keys
  `T` does not declare under `:undeclared`, the checks run anyway. Where [[defproven-in]]
  defined `T`, which then has no drafts, the answer is what [[check]] with `sel` answers of a
  value of `T` holding those entries of the map whose keys `T` declares, with the other keys
  under `:undeclared`. A map is any map: a plain map, a record, or a draft or a value of any
  type, displaced or not, whose entries are read and whose memory is neither read nor written.

  One pass over every map, so the maps share each source's calls as in [[check-all]]. A report
  holds under `:missing` the required fields a map lacks whose presence `sel` asks, as
  [[check]]'s does. Without `sel`, or with [[every]], `sel` asks the presence of every required
  field, so, without overrides and where [[defproven]] defined `T`, the answer is true exactly
  when [[seal]] of a draft holding the map would seal.

  `overrides` maps a source to a function of the source's shape, keys in and a map from each
  key to its answer out. For this call only, every read of the source in the checks the call
  runs calls that function, and the source is not called. Any other run, on this thread or
  another, reads the source itself. No draft is made and nothing is remembered, so no value
  proves a check that passed under an override.

  Throws ex-info whose `:error` is `:recognitum/not-a-type` where `T` is not a type's class,
  `:recognitum/displaced-constructor` where `T` is the class of a displaced definition, or
  `:recognitum/not-a-map` where one of `field-maps` is not a map."
  ([T field-maps] (probe/probe-all T field-maps every nil))
  ([T field-maps sel] (probe/probe-all T field-maps sel nil))
  ([T field-maps sel overrides] (probe/probe-all T field-maps sel overrides)))

(defn probe
  "What [[probe-all]] answers of the one map `fields`: true where it would make a valid value
  of the type whose class is `T` under the checks `sel` selects, else a report. Throws as
  [[probe-all]] does.

      (rec/probe Heist fields)
      (rec/probe Heist fields rec/every {db/on-file (fn [ks] (zipmap ks (repeat true)))})"
  ([T fields] (probe/probe T fields every nil))
  ([T fields sel] (probe/probe T fields sel nil))
  ([T fields sel overrides] (probe/probe T fields sel overrides)))

(defn proven-checks
  "The ids of the checks `x` passes: all of its type's for a sealed value, and those a draft or
  a value of a [[defproven-in]] type remembers. Of a displaced definition, one that a later
  definition of its type replaced, a value has none, and a draft has those it remembers,
  though [[proves?]] of that draft is false."
  [x]
  (values/proven-checks x))

(defn proven-concerns
  "The ids of the concerns whose checks `x` passes, as [[proves?]] judges each: none for a draft
  that holds a key its type does not declare."
  [x]
  (values/proven-concerns x))

(defn checks-of
  "The ids of the checks `sel` selects in the type of `x`, which is a value, a draft or a
  type's class. A check that a selected check waits on is among them only where `sel` selects
  it too. Throws ex-info whose `:error` is `:recognitum/unknown-name` where `sel` is or holds a
  keyword that names no check of the type, no concern and no bundle check."
  [sel x]
  (values/checks-of sel x))

(defn selects-nothing?
  "Whether `sel` selects nothing in the type of `x`, a value, a draft or a type's class: none
  of its checks, and the presence of none of its required fields. A concern no check of the
  type carries, a bundle the type does not bind or a check of one, `(union)`, `(except s s)`,
  and `(reading k)` where no check reads `k` and `k` is not a required field, select nothing;
  [[every]] selects nothing only in a type with no check and no required field. [[seal]] of a
  [[defproven-in]] value by such a selection other than [[every]] throws, and [[proves?]] by
  it is false. Runs nothing; throws where `sel` names a check the type lacks, as
  [[checks-of]] does."
  [sel x]
  (values/selects-nothing? sel x))

(defn sealed?
  "Whether `x` is a value of the current definition of a [[defproven]] type. False for every
  value of a [[defproven-in]] type, whatever it has passed: proof is asked with [[proves?]]."
  [x]
  (values/sealed? x))

(defn draft?
  "Whether `x` is a draft."
  [x]
  (draft/draft? x))

(defn data-readers
  "A map from each type's tag to its `map->T`, for `clojure.edn/read` as `:readers`: one entry
  for each current type that its namespace maps its name to. An entry held across a
  redefinition of its type throws ex-info whose `:error` is
  `:recognitum/displaced-constructor`, as a held `map->T` does."
  []
  (into {} (for [[n t] (types/current-types)]
             [n #(values/make t % "Read again with the current readers: (rec/data-readers)")])))
