(ns recognitum.define
  "What `defproven` and `defproven-in` expand to. [[defproven]] splits the form into its sections,
  hands the checks sections to `recognitum.define.checks` and the sections of methods to
  `recognitum.define.methods`, and refuses the mistakes it can see. It emits one form that calls
  `recognitum.record/define-type` and defines the type's constructors, `map->T` and `->T`.
  `defchecks`, `defcopy` and `defconcern` expand through `recognitum.define.bundles`. The grammar
  that every defining form shares is in `recognitum.define.clauses`.

  Nothing here is part of the public API."
  (:require
   [clojure.set :as set]
   [clojure.string :as str]
   [recognitum.body :as body :refer [fail!]]
   [recognitum.record :as record]
   [recognitum.define.checks :refer [type-checks]]
   [recognitum.define.clauses :refer [checks-marker? id-of kind-of refuse-duplicates! refuse-meta! resolve-var]]
   [recognitum.define.methods :refer [check-method-sections! check-methods! class-named head-refusal interface-named
                                      method-fn parse-interface parse-protocol protocol-var refuse-definition!]]
   [recognitum.record.types :as types]
   [recognitum.record.values :as values]))

;;; ------------------------------------------------------------------ types

(defn- parse-sections
  "The sections after the fields, in the order written, each headed by its `:marker`:

  - a checks section, `rec/checks` or a bundle binding: `{:marker :clauses}`;
  - a section of methods: `{:marker :methods}`, with the `:protocol` var or the interface `:class`
    that heads it.

  Refuses a checks section after a section of methods, a head that names a class other than an
  interface or `Object`, and metadata on a head other than a bundle binding's."
  [ctx checks-marker forms]
  (loop [items forms, cur nil, out []]
    (if-let [[x & more] (seq items)]
      (if (seq? x)
        (if cur
          (recur more (update cur (if (:clauses cur) :clauses :methods) conj x) out)
          (fail! ctx (str "expected a bundle, rec/checks, a protocol or an interface before " (pr-str x))))
        (let [done (cond-> out cur (conj cur))
              head (some #(when (:methods %) %) done)]
          (when (and (symbol? x) (or (checks-marker? checks-marker x) (protocol-var x) (interface-named x)))
            (refuse-meta! ctx x x "name"))
          (cond
            (not (symbol? x))
            (fail! ctx (str "expected a bundle, rec/checks, a protocol, an interface or a clause, got " (pr-str x)))

            (protocol-var x)
            (recur more {:protocol (protocol-var x) :marker x :methods []} done)

            (interface-named x)
            (recur more {:class (interface-named x) :marker x :methods []} done)

            head
            (fail! ctx (if (or (checks-marker? checks-marker x) (= :bundle (kind-of (resolve-var x))))
                         (str x " follows the " (if (:protocol head) "protocol " "interface ") (:marker head)
                              ": the checks sections, rec/checks and the bundle bindings, come before the protocols"
                              (when-not (:protocol head) " and interfaces"))
                         (head-refusal x)))

            (class-named x)
            (fail! ctx (head-refusal x))

            :else
            (recur more {:marker x :clauses []} done))))
      (cond-> out cur (conj cur)))))

(defn- emit-factories
  "The forms `[(def map->T ...) (def ->T ...)]` that define the constructors of type `tname`, each
  with a docstring that ends with `kind-doc`. Each constructor makes a value of the type that the
  local `t` holds."
  [tname fields kind-doc t key-of]
  (let [m (gensym "m")
        build (into {} (for [f fields] [(key-of f) f]))
        [fixed over] (split-at 20 fields)
        over-sym (gensym "overage")]
    [`(def ~(with-meta (symbol (str "map->" tname))
              {:doc (str "A " tname " holding the entries of map `m`, keyed by field keys. " kind-doc)
               :arglists `'([~'m])})
        (fn [~m] (recognitum.record.values/make ~t ~m)))
     `(def ~(with-meta (symbol (str "->" tname))
              {:doc (str "A " tname " with every field present, in order; nil is present. " kind-doc)
               :arglists `'([~@(map #(with-meta % nil) fields)])})
        (fn
          ~@(if (seq over)
              `([~@(map #(with-meta % nil) fixed) ~'& ~over-sym]
                (when-not (= (count ~over-sym) ~(count over))
                  (throw (clojure.lang.ArityException. (+ 20 (count ~over-sym)) ~(str "->" tname))))
                (let [[~@(map #(with-meta % nil) over)] ~over-sym]
                  (recognitum.record.values/make ~t ~build)))
              `([~@(map #(with-meta % nil) fields)] (recognitum.record.values/make ~t ~build)))))]))

(defn- instead
  "The remedy that ends the refusal of the class's own constructor: make a value with the
  constructors that `factories` define, each named in the namespace of `tag-sym`, the type's
  name."
  [tag-sym factories]
  (str "make a value with "
       (str/join " or " (map #(str (namespace tag-sym) "/" (second %)) factories))))

(defn- check-name-and-fields!
  "Refuses a type's name that is not a plain symbol, and fields that are not a vector of one or
  more distinct plain symbols."
  [ctx tname fields unsealed]
  (when-not (simple-symbol? tname)
    (fail! ctx (str (if unsealed "defproven-in" "defproven") " takes a plain symbol as the type's name")))
  (when-not (and (vector? fields) (every? simple-symbol? fields) (seq fields))
    (fail! ctx "fields are a vector of plain symbols"))
  (refuse-duplicates! ctx "fields" fields))

(defn- define-type-form
  "The form that defines the type: a call of `recognitum.record/define-type` on a spec and
  `wiring`. The spec holds:

  - the type's name, its fields, its checks `all`, its interfaces and its methods;
  - `:instead`, the remedy that ends the refusal of the class's own constructor;
  - for a sealed type, `:guard` and `:change`, the makers of its guards; for an unsealed type,
    `:unsealed true`."
  [tname tag-sym fields optional key-of all interfaces methods factories unsealed wiring]
  `(recognitum.record/define-type
     ~(merge
       `{:name '~tag-sym
         :fields ~(mapv (fn [f] {:key (key-of f) :sym (list 'quote f) :optional? (contains? optional f)}) fields)
         :checks ~(mapv #(select-keys % [:id :doc :concerns :waits :gate :reads :sources :fetches? :shape-of :run]) all)
         :interfaces ~interfaces
         :methods ~(into {} (for [m methods] [(:sig m) (method-fn tname fields key-of m)]))
         :instead ~(instead tag-sym factories)}
       (if unsealed
         {:unsealed true}
         `{:guard (recognitum.record.views/guard-maker)
           :change (recognitum.record.views/change-guard-maker)}))
     ~wiring))

(defn- input-bindings
  "The let bindings of the expansion that hold each bundle binding's inputs: the local that
  `input-sym` names, bound to a map from each input's keyword to its checked function."
  [bindings input-sym]
  (mapcat (fn [{:keys [sym inputs]}]
            [(input-sym sym)
             (into {} (for [[in {:keys [form]}] inputs]
                        [(keyword (name in)) (body/checked-fn form)]))])
          bindings))

(defn defproven
  "The expansion of `(rec/defproven T [fields] sections... method-sections...)`, given the
  macro's `&env` as `env` and the sections as `forms`. `opts` holds:

  - `:compile-body`, `:read-macros` and `:checks-marker`, as
    [[recognitum.define.bundles/defchecks]] takes them;
  - `:wiring`, the form of the map that `recognitum.record/define-type` takes as its second
    argument;
  - `:strategy`, the proof strategy that `:wiring` names. It answers the class's name, and here,
    at expansion, it refuses every definition that it would refuse when the type is defined;
  - `:unsealed`: where true, this is the expansion of `rec/defproven-in`, whose type is defined
    unsealed and whose constructors check nothing.

  The expansion is one form, at the top level or inside another, and its value is the type's
  class. The methods compile with the checks, before the constructors' vars are interned, so a
  method that does not compile leaves nothing. At run time, [[defined]] defines the type and
  imports its class."
  [env tname fields forms {:keys [compile-body read-macros checks-marker wiring strategy unsealed]}]
  (let [ctx {:where (str *ns* "/" tname) :call-env env :owner tname :field-word "field"
             :read-macros read-macros}
        _ (check-name-and-fields! ctx tname fields unsealed)
        fsyms (set fields)
        key-of id-of
        optional (set (filter #(:optional (meta %)) fields))
        field-map (into {} (for [f fields] [f (key-of f)]))
        fctx (assoc ctx :fields field-map :required (set/difference fsyms optional))
        all-sections (parse-sections ctx checks-marker forms)
        sections (filter :clauses all-sections)
        method-secs (remove :clauses all-sections)
        _ (check-method-sections! ctx method-secs)
        tag-sym (symbol (str *ns*) (str tname))
        classname (record/class-name strategy tag-sym)
        methods (vec (mapcat #(if (:protocol %) (parse-protocol ctx %) (parse-interface ctx %)) method-secs))
        _ (check-methods! ctx tname classname methods)
        interfaces (vec (distinct (for [s method-secs]
                                    (if (:protocol s) (:on-interface @(:protocol s)) (:class s)))))
        _ (some->> (record/refusal strategy interfaces (map :sig methods)) (refuse-definition! ctx tname methods))
        [bindings input-sym all] (type-checks ctx fctx sections checks-marker fsyms optional key-of tname compile-body)
        t (gensym "type")
        factories (emit-factories tname fields
                                  (if unsealed
                                    "Checks nothing: the value has passed nothing."
                                    "Runs every check, or throws.")
                                  t key-of)
        define-it (define-type-form tname tag-sym fields optional key-of all interfaces methods factories unsealed wiring)
        inputs (input-bindings bindings input-sym)
        new-vars (set (remove #(.getMapping *ns* %) (map second factories)))]
    `(let [~@inputs
           ~t (recognitum.define/defined ~(:where ctx) '~(ns-name *ns*) '~tname ~classname '~new-vars
                (fn [] ~define-it))]
       ~@factories
       (recognitum.record.values/value-class ~t))))

(defn defined
  "Defines the type named `tname` in the namespace named `nsym` by calling `define`, and imports
  the type's class, named `classname`, into that namespace under `tname`. Returns the type.

  Throws ex-info whose `:error` is `:recognitum/refused`, its message prefixed with `where`:

  - before calling `define`, where the namespace maps `tname` to a var, or to a class of another
    name, since the import would fail;
  - where `define` throws; the message is that of the innermost cause.

  A refused definition leaves nothing: each var of `new-vars` (the constructors' vars that the
  definition's form interned) that is still unbound is unmapped, and an earlier definition of
  the type stays current."
  [where nsym tname classname new-vars define]
  (let [n (the-ns nsym)
        previous (.getMapping n tname)
        displaced (types/named-now (symbol (str nsym) (str tname)))
        refuse (fn [^Throwable e why]
                 (doseq [s new-vars
                         :let [v (.getMapping n s)]
                         :when (and (var? v) (identical? n (.ns ^clojure.lang.Var v))
                                    (not (.hasRoot ^clojure.lang.Var v)))]
                   (ns-unmap n s))
                 (let [root (when e (last (take-while some? (iterate ex-cause e))))
                       msg (str (or why (ex-message root))
                                (if displaced
                                  (str ". " tname " keeps its earlier definition")
                                  (str ". Nothing is defined under " tname)))
                       refusal (ex-info (str where ": " msg) {:error :recognitum/refused :message msg})]
                   ;; The refusal ends the chain of causes, since the REPL prints the last
                   ;; cause's message; `e` stays with it, suppressed, for its stack trace.
                   (when e (.addSuppressed refusal e))
                   (throw refusal)))
        _ (when (and previous (not (and (class? previous)
                                        (= (.getName ^Class previous) classname))))
            (refuse nil (str tname " already names " (pr-str previous) " in " nsym
                             ", so the type's class cannot take the name")))
        type (try (define) (catch Throwable e (refuse e nil)))]
    (.importClass n tname (values/value-class type))
    type))
