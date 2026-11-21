(ns recognitum.select
  "Selections, and [[select]], which finds the checks that a selection selects in one type.

  A selection is one of:

  - a keyword: a check id or a concern id;
  - a concern, a bundle, or a bundle's check;
  - [[every]], [[shape]] or [[pure]], or what [[fetching]], [[reading]], [[except]] or
    [[union]] returns.

  A keyword names a concern or a bundle's check through a var: the var that `defconcern` or
  `defchecks` made, interned under the keyword's name in the keyword's namespace. Any other
  keyword is a type's own check id, and [[select]] refuses one that the type lacks.

  A type, here, is the map by which the record layer describes a definition. This namespace
  reads its `:name`, its `:optional`, its `:by-id`, and its `:checks`, each
  `{:id :concerns :waits :reads :sources :fetches? :shape-of}`."
  (:require
   [clojure.set :as set]))

(defrecord Concern [id doc])

(defn concern
  "The concern whose id is `id`, a qualified keyword, with the docstring `doc`."
  [id doc]
  (->Concern id doc))

(defn named
  "The concern or bundle check that keyword `k` names: the value of the var interned under
  `k`'s name in `k`'s namespace, where that is a concern or a bundle's check whose id is `k`.
  Nil otherwise."
  [k]
  (when-let [n (some-> (namespace k) symbol find-ns)]
    (when-let [v (.findInternedVar ^clojure.lang.Namespace n (symbol (name k)))]
      (when (.isBound ^clojure.lang.Var v)
        (let [x @v]
          (when (and (or (instance? Concern x) (and (map? x) (= :check (:recognitum/kind x))))
                     (= k (:id x)))
            x))))))

(def every "Selects every check." {::op :every})
(def shape "Selects every shape check: each check named after its field." {::op :shape})
(def pure "Selects every check that reads no source." {::op :pure})

(defn fetching
  "Selects the checks that read `source`."
  [source]
  {::op :fetching :source source})

(defn reading
  "Selects the checks that read the field whose key is `k`, directly or through a bundle's input."
  [k]
  {::op :reading :key k})

(defn except
  "Selects the checks that `s` selects, less those that any of `xs` selects."
  [s & xs]
  {::op :except :s s :xs (vec xs)})

(defn union
  "Selects the checks that any of `xs` selects."
  [& xs]
  {::op :union :xs (vec xs)})

(defn keywords
  "Every keyword in selection `sel`, inside `except` and `union` too."
  [sel]
  (cond (keyword? sel) [sel]
        (#{:except :union} (when (map? sel) (::op sel)))
        (mapcat keywords (cond->> (:xs sel) (= :except (::op sel)) (cons (:s sel))))
        :else []))

(defn select
  "The ids of the checks of `type` that `sel` selects, without the checks that they wait on
  ([[closure]] adds those). A selection may select nothing in `type`. Throws ex-info whose
  `:error` is:

  - `:recognitum/unknown-name` for a keyword that names no check of `type`, no concern and no
    bundle check;
  - `:recognitum/not-a-selection` where `sel` is not a selection."
  [type sel]
  (let [checks (:checks type)
        ids (set (map :id checks))
        carrying (fn [t] (set (for [c checks :when (contains? (:concerns c) t)] (:id c))))]
    (cond
      (keyword? sel) (if (contains? ids sel)
                       #{sel}
                       (let [x (named sel)]
                         (cond (instance? Concern x) (carrying sel)
                               x #{}
                               :else (throw (ex-info (str (:name type) " has no check " sel
                                                          ", and no concern or bundle check is named " sel)
                                                     {:error :recognitum/unknown-name :name sel
                                                      :type (:name type)})))))
      (instance? Concern sel) (carrying (:id sel))
      (= :check (:recognitum/kind sel)) (if (contains? ids (:id sel)) #{(:id sel)} #{})
      (= :bundle (:recognitum/kind sel)) (set/intersection ids (set (map :id (vals (:checks sel)))))
      :else
      (case (::op sel)
        :every    ids
        :shape    (set (keep #(when (:shape-of %) (:id %)) checks))
        :pure     (set (for [c checks :when (not (:fetches? c))] (:id c)))
        :fetching (set (for [c checks :when (some #(= (:source sel) %) (:sources c))] (:id c)))
        :reading  (set (for [c checks :when (contains? (:reads c) (:key sel))] (:id c)))
        :except   (set/difference (select type (:s sel)) (set (mapcat #(select type %) (:xs sel))))
        :union    (set (mapcat #(select type %) (:xs sel)))
        (throw (ex-info (str "not a selection: " (pr-str sel)) {:error :recognitum/not-a-selection
                                                                :selection sel}))))))

(defn excepted
  "Every id of `type` that an `except` inside `sel` removed."
  [type sel]
  (case (when (map? sel) (::op sel))
    :except (into (set (mapcat #(select type %) (:xs sel))) (excepted type (:s sel)))
    :union  (set (mapcat #(excepted type %) (:xs sel)))
    #{}))

(defn closure
  "`ids` and every check of `type` they wait on, directly or through others."
  [type ids]
  (loop [acc (set ids)]
    (let [more (into acc (mapcat #(get-in type [:by-id % :waits])) acc)]
      (if (= more acc) acc (recur more)))))

(defn floor
  "The shape checks of `type` that every proof of `data` needs: those of the type's required
  fields, and those of the optional fields that `data` holds."
  [type data]
  (set (for [c (:checks type) :let [k (:shape-of c)]
             :when (and k (or (not (contains? (:optional type) k)) (contains? data k)))]
         (:id c))))
