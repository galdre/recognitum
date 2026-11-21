(ns recognitum.define.checks
  "A type's checks, as `defproven` compiles them from the checks sections of a definition: its
  own clauses compiled, and the checks that each bundle binding brings, less those that an own
  check overrides. [[type-checks]] returns them, or throws the refusal of the definition where a
  binding, a check, an override or a wait is wrong. Hidden: how bindings, own checks, overrides
  and waits are read."
  (:require
   [clojure.string :as str]
   [recognitum.body :as body :refer [fail!]]
   [recognitum.define.bundles :refer [input-key]]
   [recognitum.define.clauses :refer [checks-marker? kind-of parse-clause refuse-duplicates! resolve-var
                                      sourced-reads topo-check! words]]
   [recognitum.define.methods :refer [head-refusal]]
   [recognitum.record :as record]))

(defn- binding-gate
  "The `:when-extant` field of a bundle binding, or nil: the field that `^{:when-extant field}`
  names on the binding's head, `marker`. While that field is absent, the binding's checks pass
  without running. Refuses any other metadata key, and a field that is not an optional field
  of the type."
  [ctx marker fsyms optional]
  (let [mm (dissoc (meta marker) :line :column :end-line :end-column :file)]
    (when-let [bad (seq (remove #{:when-extant} (keys mm)))]
      (fail! ctx (str "unknown flag ^" (first bad) " on the binding of " marker ". Flags: ^{:when-extant field}")))
    (when (contains? mm :when-extant)
      (let [f (:when-extant mm)
            head (str "^{:when-extant " (pr-str f) "} on " marker ": ")]
        (cond
          (not (simple-symbol? f))
          (fail! ctx (str head "name a field, as a plain symbol"))
          (not (fsyms f))
          (fail! ctx (str head f " is not a field of " (:owner ctx) ". Optional fields: " (words (sort optional))))
          (not (optional f))
          (fail! ctx (str head f " is a required field, so it is never absent and the binding never skips."
                          " Optional fields: " (words (sort optional))))
          :else f)))))

(defn- parse-binding
  "A bundle binding, parsed: `{:var :sym :bundle :inputs :gate}`. `:sym` is the bundle's
  qualified name; `:inputs` maps each input's symbol to its clause's `{:reads :form}`, as
  [[recognitum.body/analyze]] returns them; `:gate` is the key of the binding's `:when-extant`
  field, or nil. Refuses a head that is not a bundle, an input clause that names no input of
  the bundle, has waits or is written twice, and an input that no clause binds."
  [ctx fctx {:keys [marker clauses]} fsyms optional key-of]
  (let [v (resolve-var marker)
        _ (when-not (= :bundle (kind-of v))
            (fail! ctx (head-refusal marker)))
        b @v
        ins (set (:inputs b))
        parsed (for [c clauses]
                 (let [{:keys [name waits body line]} (parse-clause (assoc ctx :input-of marker) c)
                       cctx (assoc fctx :line line :fetch? false
                                   :no-fetch (str "input clause " name))]
                   (when-not (ins name)
                     (fail! cctx (str "input clause " name ": bundle " marker " has no input " name
                                      ". Its inputs: " (words (:inputs b)))))
                   (when (seq waits) (fail! cctx (str "input clause " name " takes no waits")))
                   (let [{:keys [form reads]} (body/analyze (assoc cctx :clause (str "input clause " name " of " marker)) body)]
                     [name {:reads reads :form form}])))
        given (into {} parsed)]
    (refuse-duplicates! ctx (str "input clauses of " marker) (map first parsed))
    (when-let [missing (seq (remove given (:inputs b)))]
      (fail! ctx (str "no clause binds input " (str/join ", " missing) " of bundle " marker)))
    {:var v :sym (:name b) :bundle b :inputs given
     :gate (some-> (binding-gate fctx marker fsyms optional) key-of)}))

(defn- check-ref
  "What the qualified symbol `s` names in a wait or an override: a check of a bundle bound here,
  or a bundle bound here. Refuses anything else; `what` opens the message."
  [cctx bound tname s what]
  (let [v (resolve-var s)]
    (case (kind-of v)
      :check (let [c @v
                   bv (resolve-var (:bundle c))]
               (when-not (and bv (contains? (:checks @bv) (:name c)))
                 (fail! cctx (str what " " s ": " (:bundle c) " no longer defines it")))
               (when-not (bound (:bundle c))
                 (fail! cctx (str what " " s ": it is not a check of any bundle bound here."
                                  " Its bundle " (:bundle c) " is not bound in " tname)))
               c)
      :bundle (if (bound (:name @v))
                @v
                (fail! cctx (str what " " s ": bundle " (:name @v) " is not bound in " tname)))
      (fail! cctx (str what " " s (if v
                                    ": it is not a check of any bundle bound here, nor a bundle"
                                    ": no such var"))))))

(defn- own-wait-ids
  "The ids of the checks that own check `name` waits on. Each symbol of `waits` names:

  - by a plain symbol, an own check;
  - by a qualified symbol, a check of a bound bundle, or a bound bundle, whose every check is
    waited on.

  Refuses any other wait."
  [cctx own-names key-of tname bound name waits]
  (set (mapcat (fn [w]
                 (cond
                   (simple-symbol? w)
                   (if (own-names w)
                     [(key-of w)]
                     (let [v (resolve-var w)
                           kind (kind-of v)]
                       (fail! cctx (str "wait " w " of " name " is not a check of " tname
                                        ". Its own checks: " (words (sort own-names))
                                        (when (#{:bundle :check} kind)
                                          (str ". A wait on a bundle"
                                               (when (= :check kind) "'s check")
                                               " is qualified: " (symbol v)))))))
                   (qualified-symbol? w)
                   (let [r (check-ref cctx bound tname w "wait")]
                     (if (= :bundle (:recognitum/kind r))
                       (map :id (vals (:checks r)))
                       [(:id r)]))
                   :else (fail! cctx (str "a wait is a symbol: " (pr-str w)))))
               waits)))

(defn- own-check
  "One own clause, parsed, compiled to the check that `recognitum.record/define-type` takes. A
  clause with `:override` replaces the check of a bound bundle that its qualified name names: it
  keeps that check's id, adds that check's concerns to its own, and takes its binding's
  `:when-extant` field."
  [{:keys [fctx fsyms own-names bound gate-of tname key-of compile-body]}
   {:keys [name waits body override? concerns line doc]}]
  (let [cctx (assoc fctx :line line :fetch? true)
        target (cond
                 (and override? (qualified-symbol? name))
                 (let [r (check-ref cctx bound tname name ":override")]
                   (when-not (= :check (:recognitum/kind r))
                     (fail! cctx (str ":override " name " names a bundle, not one of its checks")))
                   r)
                 override? (fail! cctx (str ":override needs a qualified bundle check, got " name))
                 (qualified-symbol? name)
                 (fail! cctx (str name " is qualified: write :override after its waits to replace that bundle check"))
                 :else nil)
        wait-ids (own-wait-ids cctx own-names key-of tname bound name waits)
        {:keys [form reads sources fetches?]} (body/analyze (assoc cctx :clause (str "check " name)) body)
        gate (when target (gate-of (:bundle target)))]
    {:id (if target (:id target) (key-of name)) :doc doc
     :concerns (into concerns (:concerns target)) :waits wait-ids :override-of (:bundle target) :gate gate
     :shape-of (when (and (simple-symbol? name) (fsyms name)) (key-of name))
     :reads (cond-> (set (map key-of reads)) gate (conj gate))
     :sources sources :fetches? fetches?
     :run (compile-body (sourced-reads form))}))

(defn- bundle-checks-of
  "The checks that `bindings` bring, each bundle's in its order, less those whose ids are in
  `overridden`. Each check reads the fields that its inputs read, and runs the bundle's check on
  the inputs that its binding's local holds; `input-sym` names that local."
  [bindings overridden key-of input-sym]
  (vec (for [{:keys [bundle sym inputs gate]} bindings
             n (:order bundle)
             :let [c (get-in bundle [:checks n])]
             :when (not (overridden (:id c)))]
         {:id (:id c) :doc (:doc c) :concerns (:concerns c) :waits (:waits c) :gate gate
          :reads (cond-> (set (map key-of (mapcat #(get-in inputs [% :reads]) (:input-reads c))))
                   gate (conj gate))
          :sources `(get-in @(var ~sym) [:checks '~n :sources])
          :fetches? (:fetches? c)
          :run `(recognitum.record/bound-check (get-in @(var ~sym) [:checks '~n :run])
                                               (select-keys ~(input-sym sym) ~(mapv input-key (sort (:input-reads c)))))})))

(defn- check-waits!
  "Refuses a check of `all` that waits on a check not among the `known` ids, and waits that
  form a cycle."
  [ctx all known]
  (doseq [c all, w (:waits c)]
    (when-not (known w)
      (fail! ctx (str (:id c) " waits on " w ", which an override or a binding left out"))))
  (let [explicit (into {} (map (juxt :id (comp set :waits))) all)]
    (topo-check! ctx (map :id all) (record/waits-of all)
                 (fn [a b] (not (contains? (explicit a) b))))))

(defn type-checks
  "The checks of a type, from its checks `sections`, as `[bindings input-sym all]`:

  - `bindings`, its bundle bindings, parsed;
  - `input-sym`, a map from each binding's bundle name to the local that holds its inputs;
  - `all`, every check: the own clauses compiled, then the checks that the bindings bring.

  Refuses `rec/checks` written twice, a bundle bound twice, two clauses or two checks of one
  name, a wait on a check that is left out, and waits that form a cycle."
  [ctx fctx sections checks-marker fsyms optional key-of tname compile-body]
  (let [own-secs (filter #(checks-marker? checks-marker (:marker %)) sections)
        _ (when (> (count own-secs) 1) (fail! ctx "rec/checks appears twice"))
        bindings (vec (for [s sections :when (not (checks-marker? checks-marker (:marker s)))]
                        (parse-binding ctx fctx s fsyms optional key-of)))
        _ (refuse-duplicates! ctx "bindings of a bundle" (map :sym bindings))
        bound (set (map :sym bindings))
        own (mapv #(parse-clause ctx %) (mapcat :clauses own-secs))
        _ (refuse-duplicates! ctx "clauses" (map :name own))
        own-checks (mapv #(own-check {:fctx fctx :fsyms fsyms :tname tname :key-of key-of
                                      :own-names (set (filter simple-symbol? (map :name own)))
                                      :bound bound :gate-of (into {} (map (juxt :sym :gate)) bindings)
                                      :compile-body compile-body}
                                     %)
                         own)
        overridden (set (keep #(when (:override-of %) (:id %)) own-checks))
        input-sym (into {} (map-indexed (fn [i b] [(:sym b) (gensym (str "inputs" i))])) bindings)
        bundle-checks (bundle-checks-of bindings overridden key-of input-sym)
        all (into own-checks bundle-checks)
        _ (refuse-duplicates! ctx "checks" (map :id all))
        known (set (map :id all))
        _ (check-waits! ctx all known)]
    [bindings input-sym all]))
