(ns recognitum.define.clauses
  "What every defining macro reads alike:

  - what a definition's symbols name: [[resolve-var]], [[kind-of]], [[checks-marker?]],
    [[id-of]];
  - one clause of checks, with its flags and docstring: [[parse-clause]];
  - a body's reads of sources, written through `recognitum.record.probe/sourced`:
    [[sourced-reads]];
  - the refusals that every defining form shares: [[refuse-meta!]], [[topo-check!]],
    [[refuse-duplicates!]].

  Each function returns a form or data, or throws the refusal of a definition. Hidden: the
  grammar of a clause's flags and the remedies that its refusals write."
  (:require
   [clojure.string :as str]
   [recognitum.body :as body :refer [fail!]]
   [recognitum.record.probe :as probe]))

;;; ------------------------------------------------------------------ reads of sources

(defn sourced-reads
  "`form`, a body's `:form` as [[recognitum.body/analyze]] returns it, with the source of each
  `(&fetch src k)` and `(&fetch-each src ks)` written as `(recognitum.record.probe/sourced src)`,
  so that a probe's overrides answer in the source's place. A quoted form is data and stays as it
  is."
  [form]
  (cond (seq? form)
        (let [h (first form)
              out (cond (= 'quote h) form
                        (contains? '#{&fetch &fetch-each} h)
                        (let [[_ src k] form]
                          (list h (list `probe/sourced (sourced-reads src)) (sourced-reads k)))
                        :else (apply list (map sourced-reads form)))]
          (if (and (meta form) (not (identical? out form))) (with-meta out (meta form)) out))
        (map-entry? form) (mapv sourced-reads form)
        (coll? form) (into (empty form) (map sourced-reads) form)
        :else form))

;;; ------------------------------------------------------------------ names

(defn resolve-var [s] (try (let [v (resolve s)] (when (var? v) v)) (catch Exception _ nil)))

(defn kind-of [v] (when (var? v) (let [x @v] (when (map? x) (:recognitum/kind x)))))

(defn checks-marker?
  "Whether `s` is a symbol that resolves to the var named by `marker`, the var that starts a
  section of own checks (`rec/checks`)."
  [marker s]
  (and (symbol? s) (= marker (some-> (resolve-var s) symbol))))

(defn id-of [nm] (keyword (str *ns*) (str nm)))

(defn- named-var
  "The var that the name of keyword `k` resolves to in the keyword's namespace, or nil."
  [k]
  (when-let [n (find-ns (symbol (namespace k)))]
    (let [v (ns-resolve n (symbol (name k)))]
      (when (var? v) v))))

(defn- concern-var
  "The concern var whose id is keyword `k`, or nil: the var that `rec/defconcern` defined under
  the keyword's name, in the keyword's namespace."
  [k]
  (when-let [v (named-var k)]
    (when (and (:recognitum/concern (meta v)) (= k (keyword (symbol v)))) v)))

(defn- symbol-concern
  "The id of the concern that symbol `s` names, where `s` resolves to a var that `rec/defconcern`
  defined; nil where `s` names no concern."
  [s]
  (when-let [v (resolve-var s)]
    (when (:recognitum/concern (meta v)) (keyword (symbol v)))))

(defn words [xs] (str/join " " xs))

;;; ------------------------------------------------------------------ clauses

(def ^:private reader-meta #{:line :column :end-line :end-column :file :source})

(defn- show-flag
  "Keyword `k` as written in this namespace: `::name` where it is of this namespace."
  [k]
  (if (= (namespace k) (str *ns*)) (str "::" (name k)) (str k)))

(defn- show-flags
  "The flags `x`, a keyword, a symbol or a set, as written in this namespace; a set's members
  sorted as text."
  [x]
  (let [one #(if (keyword? %) (show-flag %) (pr-str %))]
    (if (set? x) (str "#{" (str/join " " (sort (map one x))) "}") (one x))))

(def ^:private input-remedy
  "an input clause takes no concern or :override; they go after a check's waits")

(defn refuse-meta!
  "Refuses metadata written on `x`: a clause, its name or its waits, or a section's head. The
  macros read no metadata there, and ignore what the reader adds (`:line` and the like). `place`
  describes `x` in the message, and `nm` names the clause in the remedy. With `:input-of` in
  `ctx`, the clause binds an input of that bundle, and the remedy is an input clause's."
  [ctx place x nm]
  (when-let [m (not-empty (apply dissoc (meta x) reader-meta))]
    (let [shown (str/join " " (for [[k v] m]
                                (if (and (true? v) (keyword? k)) (str "^" (show-flag k)) (str "^" (pr-str {k v})))))
          k (some #(when (or (qualified-keyword? %) (= :override %)) %) (keys m))]
      (fail! ctx (str shown " on " place ": "
                      (if (:input-of ctx)
                        input-remedy
                        (str "a clause takes no metadata; its concerns and :override go after its waits, as in ("
                             nm " [waits] " (if k (show-flag k) "::concern") " body)")))))))

(defn- not-the-id!
  "Refuses keyword `k` among the flags of clause `nm`: `k` is not a concern's id, but its name
  resolves, in its namespace, to the concern var `v`, which a namespace other than `k`'s defines.
  The message gives the two right spellings of the concern."
  [ctx nm k v]
  (let [id (keyword (symbol v))
        short (symbol (name k))
        sym (if (= v (resolve-var short)) short (symbol v))]
    (fail! ctx (str (show-flag k) " on " nm " is not the id of a concern: " short
                    (if (= (namespace k) (str *ns*)) " here" (str " in " (namespace k)))
                    " is the concern " (symbol v) ", whose id is " id ". Write " sym " or " id))))

(defn- clause-flags
  "The flags `x` written after the waits of clause `nm`, as a set of keywords: `:override` and
  the ids of concerns that `rec/defconcern` defined. `x` is a keyword, a symbol or a set of them.
  A symbol names the concern whose var it resolves to; a keyword names the concern whose id it
  is. Refuses any other flag."
  [ctx nm x]
  (set (for [k (if (set? x) x #{x})]
         (cond (= :override k) k
               (qualified-keyword? k)
               (let [v (named-var k)]
                 (cond (concern-var k) k
                       (and v (:recognitum/concern (meta v))) (not-the-id! ctx nm k v)
                       :else (fail! ctx (str (show-flag k) " on " nm " names no concern that rec/defconcern defines"))))
               (keyword? k)
               (fail! ctx (str "unknown flag " k " on " nm ": a clause's flags are :override and concerns"))
               (symbol? k)
               (or (symbol-concern k)
                   (fail! ctx (str k " on " nm " is not a concern: a symbol after a clause's waits names"
                                   " a concern that rec/defconcern defines")))
               :else
               (fail! ctx (str "a clause's flags are keywords and concerns' symbols: " (show-flags x) " on " nm))))))

(defn- flags-written
  "The flags of a clause, or nil where it has none. `more` is the forms after the clause's waits.
  Its first form is the flags where another form follows it and it is a keyword, a set or a
  symbol. In an input clause (`:input-of` in `ctx`), which takes no flags, a symbol is returned
  only where it names a concern, and the caller refuses what is returned; any other symbol is
  the clause's body."
  [ctx more]
  (let [x (first more)]
    (when (and (next more)
               (or (keyword? x) (set? x)
                   (and (symbol? x) (or (not (:input-of ctx)) (symbol-concern x)))))
      x)))

(defn- flag-form?
  "Whether `x` reads only as a flag: a keyword, a symbol that names a concern, or a set holding
  one of those."
  [x]
  (let [flag? #(or (keyword? %) (and (symbol? %) (symbol-concern %)))]
    (boolean (or (flag? x) (and (set? x) (some flag? x))))))

(defn- clause-head
  "The text of clause `nm` as it should be written, up to its body: its waits; the flags in
  `flags` (keywords, symbols and sets of them; nils are left out), as one set where there are
  several; and `\"...\"` in place of the docstring where `doc` is not nil."
  [nm waits flags doc]
  (let [fs (distinct (mapcat #(if (set? %) (sort-by show-flags %) [%]) (remove nil? flags)))]
    (str "(" (pr-str nm) " " (pr-str waits) " " (show-flags (if (next fs) (set fs) (first fs)))
         (when doc " \"...\""))))

(defn- concern-keyword?
  "Whether `x` is a keyword that is a concern's id."
  [x]
  (boolean (and (qualified-keyword? x) (concern-var x))))

(defn- refuse-flag-alone!
  "Refuses check clause `nm` where `x`, the one form of its body after its flags and docstring,
  is a concern: a concern's id, a symbol that names a concern, or a set holding one of those.
  Such a form reads as a flag, so the clause has flags and no body. Where `x` is a keyword whose
  name resolves to a concern's var but that is not the concern's id, or a set holding one,
  refuses it as [[not-the-id!]] does."
  [ctx nm waits written doc x]
  (let [one? #(or (concern-keyword? %) (and (symbol? %) (symbol-concern %)))
        not-id (fn [k] (when (and (qualified-keyword? k) (not (concern-var k)))
                         (when-let [v (named-var k)] (when (:recognitum/concern (meta v)) v))))]
    (cond
      (or (one? x) (and (set? x) (some one? x)))
      (fail! ctx (str (show-flags x) ", the whole body of " nm ", is a flag, so " nm " has flags and no"
                      " body: a concern after a clause's waits is one of its flags, and the body follows"
                      " the flags, as in " (clause-head nm waits [written x] doc) " body)"))
      (and (keyword? x) (not-id x)) (not-the-id! ctx nm x (not-id x))
      (set? x) (when-let [k (some #(when (and (keyword? %) (not-id %)) %) x)] (not-the-id! ctx nm k (not-id k))))))

(defn- refuse-misplaced!
  "Refuses `body`, the forms of clause `nm` after its flags and docstring, where a form before the
  last is a flag ([[flag-form?]]). No flag is read in a body, and such a form, evaluated as a
  statement, does nothing. The message says where the forms are, and writes the clause's head
  with them among its flags."
  [ctx nm waits written doc body]
  (let [before (butlast body)]
    (when-let [found (seq (filter flag-form? before))]
      (let [shown (map show-flags found)
            listed (if (next shown) (str (str/join ", " (butlast shown)) " and " (last shown)) (first shown))
            what (if-let [b (:input-of ctx)] (str "input clause " nm " of " b) nm)
            place (cond (not= (first found) (first before)) (str "after other forms in the body of " what)
                        doc (str "after the docstring of " what)
                        written (str "after " (show-flags written) " on " what)
                        :else (str "in the body of " what))
            head (str (clause-head nm waits (cons written found) doc) " ...)")]
        (fail! ctx (str listed ", written " place ", " (if (next found) "are" "is")
                        " in the body, where no flag is read: "
                        (if (:input-of ctx)
                          input-remedy
                          (str "a clause's flags follow its waits, before its docstring, and several go"
                               " in one set, as in " head))))))))

(defn parse-clause
  "Parses `clause`, `(name [waits] flags? \"doc\"? body...)`, where `flags` is a keyword, a
  symbol or a set of them: the clause's concerns and `:override`. Returns
  `{:name :waits :doc :concerns :override? :line :body}`; `:body` is one form, and a body of
  several forms is wrapped in `do`.

  Refuses:

  - a clause of another shape, and a clause with no body;
  - metadata on the clause, its name or its waits;
  - a flag that names no concern and is not `:override`;
  - a body that holds a flag before its last form;
  - a check's body that is one form and a concern.

  With `:input-of` in `ctx`, the clause binds an input of that bundle and takes no flags, and a
  body of one form is the input's value, whatever that form is."
  [ctx clause]
  (let [ctx (assoc ctx :line (:line (meta clause)))]
    (when-not (and (seq? clause) (symbol? (first clause)) (vector? (second clause)))
      (fail! ctx (str "a clause is (name [waits] flags? \"doc\"? body): " (pr-str clause))))
    (let [[nm waits & more] clause
          what (if-let [b (:input-of ctx)] (str "input clause " nm " of " b) nm)
          _ (refuse-meta! ctx (if (:input-of ctx) what (str "the clause " nm)) clause nm)
          _ (refuse-meta! ctx (str "the name of " what) nm nm)
          _ (refuse-meta! ctx (str "the waits of " what) waits nm)
          written (flags-written ctx more)
          _ (when (and written (:input-of ctx))
              (fail! ctx (str (show-flags written) " on " what ": " input-remedy)))
          flags (if written (clause-flags ctx nm written) #{})
          more (if written (rest more) more)
          [doc body] (if (and (string? (first more)) (next more)) [(first more) (rest more)] [nil more])]
      (when (empty? body) (fail! ctx (str nm " has no body")))
      (refuse-misplaced! ctx nm waits written doc body)
      (when (and (not (:input-of ctx)) (not (next body)))
        (refuse-flag-alone! ctx nm waits written doc (first body)))
      {:name nm :waits waits :doc doc :concerns (disj flags :override) :line (:line (meta clause))
       :override? (contains? flags :override)
       :body (if (next body) (cons 'do body) (first body))})))

(defn topo-check!
  "Refuses waits that form a cycle among the checks `ids`; `waits-of` gives the ids that a check
  waits on. `read-wait?`, given a check and a check that it waits on, says whether the wait comes
  from a read rather than from the check's wait vector; where one does, the message says so."
  ([ctx ids waits-of] (topo-check! ctx ids waits-of (constantly false)))
  ([ctx ids waits-of read-wait?]
   (let [state (atom {})]
     (letfn [(visit [id path]
               (case (@state id)
                 :done nil
                 :active (let [ring (conj (subvec path (.indexOf ^java.util.List path id)) id)]
                           (fail! ctx (str "the waits form a cycle: " (str/join " -> " ring)
                                           (when (some (fn [[a b]] (read-wait? a b)) (partition 2 1 ring))
                                             " (a check waits on the shape checks of the fields it reads)"))))
                 (do (swap! state assoc id :active)
                     (doseq [w (waits-of id)] (visit w (conj path id)))
                     (swap! state assoc id :done))))]
       (doseq [id ids] (visit id []))))))

(defn refuse-duplicates! [ctx what names]
  (when-let [d (first (for [[n c] (frequencies names) :when (> c 1)] n))]
    (fail! ctx (str "two " what " are named " d))))
