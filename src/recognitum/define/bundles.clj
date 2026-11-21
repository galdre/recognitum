(ns recognitum.define.bundles
  "Bundles and concerns:

  - [[defchecks]], [[defcopy]] and [[defconcern]] are what `rec/defchecks`, `rec/defcopy` and
    `rec/defconcern` expand to;
  - [[check-of]] and [[copy-bundle]] are what the expansions call at run time, to make the value
    of a check's var and to copy a bundle with its checks renamed;
  - [[input-key]] is the key under which a bundle's check reads an input.

  Hidden: how a bundle's checks compile and become vars."
  (:require
   [recognitum.body :as body :refer [fail!]]
   [recognitum.define.clauses :refer [checks-marker? id-of kind-of parse-clause refuse-duplicates! refuse-meta!
                                      resolve-var sourced-reads topo-check! words]]
   [recognitum.select :as select]))

;;; ------------------------------------------------------------------ bundles

(defn check-of
  "The value of the var of check `cname` of `bundle`."
  [bundle cname]
  (assoc (select-keys (get-in bundle [:checks cname]) [:id :name :doc :concerns :waits])
         :recognitum/kind :check :bundle (:name bundle)))

(defn input-key [s] (keyword (name s)))

(defn- named
  "`nm` with the docstring `doc`, or as it is when `doc` is nil."
  [nm doc]
  (cond-> nm doc (vary-meta assoc :doc doc)))

(defn- emit-check-vars [bname cs]
  (for [c cs]
    `(def ~(named (:name c) (:doc c))
       (check-of ~bname '~(:name c)))))

(defn- compile-bundle-checks
  "The `parsed` clauses of the bundle `bname`, each compiled: its id, the ids it waits on
  among the bundle's check `names`, the inputs it reads, its sources, and its run. Refuses a
  check whose name is not a plain symbol, and a wait on a check that the bundle does not have."
  [ctx env bname fields names compile-body parsed]
  (vec (for [{:keys [name waits body] :as c} parsed
             :let [cctx (assoc ctx :line (:line c) :fields fields :required #{}
                               :owner bname :field-word "input" :call-env env :fetch? true)
                   _ (when-not (simple-symbol? name)
                       (fail! cctx (str "a bundle's check is named by a plain symbol: " name)))
                   wait-ids (set (for [w waits]
                                   (if (and (simple-symbol? w) (names w))
                                     (id-of w)
                                     (fail! cctx (str "wait " w " of " name " is not a check of " bname
                                                      ". Its checks: " (words (sort names)))))))
                   {:keys [form reads sources fetches?]} (body/analyze (assoc cctx :clause (str "check " name)) body)]]
         (assoc c :id (id-of name) :waits wait-ids :input-reads reads
                :sources sources :fetches? fetches? :run (compile-body (sourced-reads form))))))

(defn defchecks
  "The expansion of `(rec/defchecks bname \"doc\"? [inputs] rec/checks clauses...)`, which
  defines the bundle's var and a var for each check, and evaluates to the bundle's var. `doc` is
  nil where the form has none, and `marker` is the form written where `rec/checks` belongs.
  `opts` holds:

  - `:compile-body`, the engine's compiler of a check body;
  - `:read-macros`, as [[recognitum.body/analyze]] takes it;
  - `:checks-marker`, the symbol of the var that starts a section of own checks."
  [env bname doc inputs marker clauses {:keys [compile-body read-macros checks-marker]}]
  (let [ctx {:where (str *ns* "/" bname) :read-macros read-macros}
        _ (when-not (and (simple-symbol? bname) (vector? inputs) (every? simple-symbol? inputs))
            (fail! ctx (str "defchecks takes a name, a docstring if any, a vector of plain input symbols,"
                            " rec/checks and clauses")))
        _ (when-not (checks-marker? checks-marker marker)
            (fail! ctx (str "expected rec/checks after the inputs, got " (pr-str marker))))
        _ (refuse-meta! ctx marker marker "name")
        _ (refuse-duplicates! ctx "inputs" inputs)
        parsed (mapv #(parse-clause ctx %) clauses)
        _ (when-let [c (first (filter :override? parsed))]
            (fail! (assoc ctx :line (:line c))
                   (str ":override on " (:name c) ": a bundle's check replaces no check; :override is for a"
                        " clause of a type that replaces a check of a bound bundle")))
        names (set (map :name parsed))
        _ (refuse-duplicates! ctx "checks" (map :name parsed))
        fields (into {} (map (juxt identity input-key)) inputs)
        cs (compile-bundle-checks ctx env bname fields names compile-body parsed)
        _ (topo-check! ctx (map :id cs) (into {} (map (juxt :id :waits)) cs))]
    `(do
       (def ~(named bname doc)
         {:recognitum/kind :bundle
          :name '~(symbol (str *ns*) (str bname))
          :inputs '~inputs
          :order '~(mapv :name cs)
          :checks ~(into {} (for [c cs]
                              [(list 'quote (:name c))
                               {:id (:id c) :name (list 'quote (:name c)) :doc (:doc c) :concerns (:concerns c)
                                :waits (:waits c) :input-reads (list 'quote (:input-reads c))
                                :sources (:sources c) :fetches? (:fetches? c) :run (:run c)}]))})
       ~@(emit-check-vars bname cs)
       (var ~bname))))

(defn copy-bundle
  "`bundle` with its checks renamed by `renames` and their ids in the namespace of `qname`."
  [bundle renames qname]
  (let [rid #(keyword (namespace qname) (str (renames %)))
        id->name (into {} (for [[n c] (:checks bundle)] [(:id c) n]))]
    (assoc bundle
           :name qname
           :order (mapv renames (:order bundle))
           :checks (into {} (for [[n c] (:checks bundle)]
                              [(renames n) (assoc c :name (renames n) :id (rid n)
                                                  :waits (set (map (comp rid id->name) (:waits c))))])))))

(defn defcopy
  "The expansion of `(rec/defcopy new-name \"doc\"? bundle {check new-check ...})`, given the
  forms after the name."
  [new-name args]
  (let [ctx {:where (str *ns* "/" new-name)}
        [doc orig renames & more] (if (string? (first args)) args (cons nil args))
        _ (when (or more (< (count args) 2))
            (fail! ctx "defcopy takes a name, a docstring if any, a bundle and a map {check new-name ...}"))
        ov (resolve-var orig)
        _ (when-not (= :bundle (kind-of ov))
            (fail! ctx (str orig (if ov " is not a bundle" " names no bundle var"))))
        b @ov
        _ (when-not (and (map? renames) (every? simple-symbol? (keys renames)) (every? simple-symbol? (vals renames)))
            (fail! ctx (str "defcopy takes a map from each check of " orig " to its new name: {check new-name ...}")))
        missing (remove (set (keys renames)) (:order b))
        extra (remove (set (:order b)) (keys renames))
        _ (when (or (seq missing) (seq extra))
            (fail! ctx (str "the map must name every check of " orig " exactly once."
                            (when (seq missing) (str " Missing: " (words missing) "."))
                            (when (seq extra) (str " Not checks of " orig ": " (words extra) "."))
                            " Its checks: " (words (:order b)))))
        _ (when-let [d (first (for [[n c] (frequencies (vals renames)) :when (> c 1)] n))]
            (fail! ctx (str "two checks get the same new name: " d)))
        qname (symbol (str *ns*) (str new-name))
        _ (doseq [n (vals renames)]
            (when (= n new-name) (fail! ctx (str "new name " n " is the copy's own name")))
            (when-let [v (resolve-var n)]
              (when (and (= (str *ns*) (namespace (symbol v))) (#{:check :bundle} (kind-of v))
                         (not= (:bundle @v) qname))
                (fail! ctx (str "new name " n " would redefine " (symbol v))))))
        cs (vals (:checks (copy-bundle b renames qname)))]
    `(do
       (def ~(named new-name doc) (copy-bundle (deref (var ~(:name b))) '~renames '~qname))
       ~@(emit-check-vars new-name cs)
       (var ~new-name))))

(defn defconcern
  "The expansion of `(rec/defconcern name \"doc\")`."
  [tname doc]
  (when-not (and (simple-symbol? tname) (string? doc))
    (fail! {:where (str *ns* "/" tname)} "defconcern takes a name and a docstring"))
  `(def ~(vary-meta tname assoc :doc doc :recognitum/concern true) (select/concern ~(id-of tname) ~doc)))
