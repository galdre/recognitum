(ns recognitum.record.values
  "Values and drafts of any type, made and changed through the type's installed write:

  - [[make]], [[draft]], [[clean]] and [[seal]] make values and drafts;
  - [[sealed?]], [[proves?]], [[proven-checks]] and [[proven-concerns]] answer what a value or
    a draft is known to pass, and [[checks-of]] and [[selects-nothing?]] what a selection
    names in its type.

  A **sealed value** is a value of a type's class that the current definition of the type
  proved. The only paths to one run the type's checks: [[make]], [[seal]], and a write
  (`assoc`, `dissoc`, `conj`, `merge`, `into`) on a sealed value, which reruns the checks that
  read a key it changes and seals the result or throws. A **draft** is an unchecked map of a
  type that remembers which checks pass on its entries; a write to it forgets the checks that
  read a key written.

  A type defined with `:unsealed true` has no sealed values and no drafts. Its values are
  made and written without checks and hold, in place, what a draft remembers: the checks
  that passed on their entries. Such a value is never sealed; [[proves?]] asks its memory.

  Every type is closed: a value refuses a key its type does not declare, and a draft holding
  one does not seal. A required field must be present in a sealed value.

  Hidden: which arm of the installed write each operation calls, and the rules for values of
  a displaced definition."
  (:require
   [clojure.set :as set]
   [recognitum.proof :as proof]
   [recognitum.record.draft :refer [draft? marks-of]]
   [recognitum.record.memory :refer [passes]]
   [recognitum.record.reports :refer [displaced-draft displaced-refusal displaced-unsealed missing no-definition
                                      no-drafts]]
   [recognitum.record.selection :refer [nothing? refused-for? selects-nothing-refusal]]
   [recognitum.record.types :refer [current? gate named-now refuse-type! type-of type-of! value-type!]]
   [recognitum.select :as select])
  (:import
   [recognitum.record.draft Draft]))

(defn with-meta-of
  "`m` with the meta of `x`: `m` itself where it holds that meta already."
  [m x]
  (let [mx (meta x)]
    (if (identical? mx (meta m)) m (with-meta m mx))))

;;; ------------------------------------------------------------------ values

(defn value-class
  "The class of `type`'s values."
  [type]
  (:recognitum.record/class type))

(defn make
  "A sealed value of `type` holding the entries of map `m`, once every check passes; for an
  unsealed type, a value of those entries, with no check run. Throws ex-info whose `:error`
  is:

  - `:recognitum/displaced-constructor` where a later definition has displaced `type`;
    `remedy`, a string, then replaces the advice to call the current `map->T`;
  - `:recognitum/undeclared-keys` where `m` holds a key the type does not declare;
  - `:recognitum/check-failed` where a check fails or a required field is absent, with the
    report under `:failed` and `:blocked`, and the absent required fields under `:missing`
    where there are any."
  ([type m] (make type m nil))
  ([type m remedy] ((gate type) :recognitum.record/make m remedy)))

(defn sealed?
  "Whether `x` is a sealed value of the current definition of its type: as the type's proof
  strategy answers, so never a value of an unsealed type."
  [x]
  (let [t (type-of x)]
    (boolean (and t (not (draft? x)) (not (class? x)) ((gate t) :recognitum.record/sealed? x nil)))))

(defn unsealed?
  "Whether `type` was defined unsealed: its values are made without checks and remember what
  passed."
  [type]
  (true? (:recognitum.record/unsealed type)))

(defn- held-memory
  "What `v`, a value of the unsealed `type`, remembers, or nil where `type` is displaced or
  `v` holds no memory."
  [type v]
  (when (current? type)
    (some-> (proof/memory (:strategy type) v) deref)))

(defn draft
  "A draft of `x`:

  - of a type's class, a new draft that holds nothing and passes nothing;
  - of a sealed value, a draft that holds its entries and passes every check;
  - of a value of a displaced definition, a draft of the type's current definition that holds
    its entries and passes nothing. Throws `:recognitum/no-current-definition` where the
    type's name no longer names a current definition of the type;
  - of a draft, that draft itself, sharing what it remembers.

  An unsealed type has no drafts: throws `:recognitum/no-drafts` for its class and its
  values."
  [x]
  (cond (draft? x) x
        (class? x) ((gate (type-of! x)) :recognitum.record/open nil nil)
        :else      (let [t (value-type! x)]
                     ;; a current unsealed type's installed write refuses ::draft-of itself
                     (if (current? t)
                       ((gate t) :recognitum.record/draft-of x nil)
                       (let [_   (when (unsealed? t) (throw (no-drafts (:name t))))
                             now (named-now (:name t))]
                         (when-not (and now (current? now)) (throw (no-definition (:name t) x)))
                         (with-meta ((gate now) :recognitum.record/rewrite ((gate now) :recognitum.record/open nil nil) (proof/plain-map x))
                           (meta x)))))))

(defn orphan?
  "Whether `x` is a value of a displaced definition whose name no longer names a current
  definition of its type, so that [[draft]] of it refuses."
  [x]
  (and (not (draft? x))
       (let [t (type-of x)]
         (and (some? t) (not (current? t))
              (let [now (named-now (:name t))]
                (not (and now (current? now))))))))

(defn clean
  "`d` without the keys its type does not declare, remembering what `d` remembers."
  [d]
  ((gate (value-type! d)) :recognitum.record/clean d nil))

(defn- not-sealable [d]
  (ex-info (str "not a draft, a sealed value or a value of an unsealed type: " (pr-str d))
           {:error :recognitum/not-a-draft :value d}))

(defn refuse-displaced!
  "Refuses `x`, a draft or a value of `type`, where a later definition displaced `type`: a draft
  as its seal does, a value as a write to it does."
  [type x]
  (when-not (current? type)
    (throw (cond (draft? x) (displaced-draft (:name type))
                 (unsealed? type) (displaced-unsealed (:name type) x)
                 :else (displaced-refusal (:name type) x)))))

(defn seal
  "Seals `d` against every check, or, where `d` is a value of an unsealed type and `sel` is
  given, against `sel`. By what `d` is:

  - a draft: returns the sealed value of its entries once every check it does not remember
    as passing passes. Before any check runs, throws `:recognitum/undeclared-keys` where it
    holds a key its type does not declare, and `:recognitum/displaced-constructor` where it is
    a draft of a displaced definition's class. Else the draft remembers each check that
    passed and forgets each that failed, whether or not the seal succeeds, and the seal
    throws as [[make]] does. `sel`, where given, must be [[recognitum.select/every]]: else
    the seal throws `:recognitum/draft-selection`, running nothing;
  - a sealed value: returns it as it is, once `sel`, where given, is read as [[proves?]] reads
    it;
  - a value of a current unsealed type: runs the checks `sel` selects, what they wait on and
    the shape checks of the fields it must or does hold, less what it is known to pass. It
    remembers what passed and forgets what failed. Returns the value itself, or throws as
    [[make]] does. Where `sel` is not every and selects nothing in its type, throws
    `:recognitum/selects-nothing` before any check runs;
  - a value of a displaced definition: throws as a write to it does, `:recognitum/displaced`;
  - a type's class or type map: throws `:recognitum/not-a-value`; anything else:
    `:recognitum/not-a-draft`."
  ([d]
   (cond (draft? d)  ((gate (type-of! d)) :recognitum.record/seal d nil)
         (sealed? d) d
         :else (let [t (type-of d)]
                 (some->> t (refuse-type! d))
                 (cond (and t (unsealed? t)) ((gate t) :recognitum.record/seal d (:ids t))
                       t (do (refuse-displaced! t d) (throw (not-sealable d)))
                       :else (throw (not-sealable d))))))
  ([d sel]
   (cond (draft? d)  (if (= select/every sel)
                       (seal d)
                       (throw (ex-info (str "a draft seals against every check, so seal takes no selection"
                                            " but rec/every for one: " (pr-str sel))
                                       {:error :recognitum/draft-selection :selection sel})))
         ;; the selection is read, as proves? reads it
         (sealed? d) (do (nothing? (type-of d) sel) d)
         :else (let [t (type-of d)]
                 (some->> t (refuse-type! d))
                 (cond (and t (unsealed? t))
                       (do (when (and (refused-for? t sel) (current? t))
                             (throw (selects-nothing-refusal t sel)))
                           ((gate t) :recognitum.record/seal d (select/select t sel)))
                       t (do (nothing? t sel) (refuse-displaced! t d) (throw (not-sealable d)))
                       :else (throw (not-sealable d)))))))

(defn passes-of
  "The checks of `type` that `x` is known to pass: every check for a sealed value; what its
  memory shows for a draft or a value of a current unsealed type; none for anything else."
  [type x]
  (cond (draft? x) (passes type (.-data ^Draft x) (marks-of x))
        (sealed? x) (:ids type)
        (unsealed? type) (passes type x (held-memory type x))
        :else #{}))

(defn data-of [x] (if (draft? x) (.-data ^Draft x) x))

(defn selects-nothing?
  "Whether `sel` selects no check of the type of `x`, a value, a draft or a type's class, and
  asks the presence of none of its required fields. `every` selects nothing only in a type
  with no check and no required field."
  [sel x]
  (nothing? (type-of! x) sel))

(defn proves?
  "Whether `x` holds every required field and passes every check that `sel` names in its
  type, every check those wait on, and the shape check of each field it must or does hold.

  Where `x` is a sealed value, a draft, or a value of an unsealed type, each of its type's
  current definition, reads `sel` first, and throws where `sel` is no selection or holds an
  unknown name. Then:

  - for a sealed value, true;
  - for a draft, false while it holds a key its type does not declare; else what its entries
    and its memory show;
  - for a value of an unsealed type, what its entries and its memory show, and false where
    `sel` is not every and selects nothing in its type.

  False, with `sel` unread, for anything else: a draft or a value of a displaced definition,
  a type's class or type map, and anything of no type."
  [x sel]
  (let [type (when-not (class? x) (type-of x))]
    (if (and type (or (draft? x) (instance? (:recognitum.record/class type) x)) (current? type))
      (let [nothing (nothing? type sel)
            whole? (fn []
                     (let [data (data-of x)]
                       (and (nil? (missing type data))
                            (set/subset? (select/closure type (into (select/select type sel)
                                                                    (select/floor type data)))
                                         (passes-of type x)))))]
        (cond (draft? x) (and (zero? (.-odd ^Draft x)) (whole?))
              (unsealed? type) (and (or (= select/every sel) (not nothing)) (whole?))
              :else (sealed? x)))
      false)))

(defn proven-checks
  "The ids of the checks `x` passes: every check of its type for a sealed value, those a draft
  or a value of an unsealed type remembers."
  [x]
  (passes-of (value-type! x) x))

(defn proven-concerns
  "The ids of the concerns whose checks `x` passes, as [[proves?]] answers for each."
  [x]
  (let [type (value-type! x)]
    (set (for [t (distinct (mapcat :concerns (:checks type)))
               :when (proves? x t)]
           t))))

(defn checks-of
  "The ids of the checks `sel` names in the type of `x`: a value, a draft or a type's class."
  [sel x]
  (select/select (type-of! x) sel))
