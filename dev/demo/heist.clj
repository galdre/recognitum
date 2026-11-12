(ns demo.heist
  "The worked example: a heist, its crew, the take and how it is split, and what the house
  has on file about the people taking it."
  (:require
   [clojure.string :as str]
   [recognitum.core :as rec]
   [demo.house :as house]))

(defn non-blank? [s] (and (string? s) (not (str/blank? s))))
(defn crew-set? [x] (and (set? x) (seq x) (every? string? x)))
(defn non-neg-int? [x] (and (int? x) (not (neg? x))))
(defn cuts-map? [x] (and (map? x) (every? string? (keys x)) (every? non-neg-int? (vals x))))
(defn sums-to [total cuts] (= total (reduce + (vals cuts))))

(rec/defproven Heist [name crew take cuts ^:optional getaway]
  rec/checks
  (name    [] "the job has a name" (non-blank? name))
  (crew    [] "the crew is a set of names" (crew-set? crew))
  (take    [] "the take is a whole number" (non-neg-int? take))
  (cuts    [] "each cut is a whole number" (cuts-map? cuts))
  (getaway [] "the getaway driver is named" (non-blank? getaway))

  (cuts-sum-to-take []
    "the cuts add up to the take"
    (sums-to take cuts))
  (only-crew-get-cuts [cuts-sum-to-take]
    "only the crew gets a cut"
    (every? crew (keys cuts)))
  (crew-vetted []
    "the house has vetted everyone on the crew"
    (every? true? (vals (rec/fetch-each house/vetted crew))))
  (getaway-not-crew []
    "the driver stays out of the vault"
    (rec/when-extant getaway (not (contains? crew getaway)))))

(def italian-job
  (map->Heist {::name "The Italian Job"
               ::crew #{"Charlie" "Stella" "Lyle"}
               ::take 3000
               ::cuts {"Charlie" 1000 "Stella" 1000 "Lyle" 1000}}))

(defn plan-from-form
  "A Heist from a form filled in field by field: any write is accepted until the seal."
  [partial-plan]
  (-> (rec/draft Heist) (into partial-plan) (rec/seal)))

(defn form-errors
  "What to tell the person who filled in the form, before anything is built: one message for
  each field left out, each key a Heist does not have, and each check the entries fail. Nil
  where `fields` would make a Heist."
  [fields]
  ;; The probe runs every check of Heist on the plain map and builds nothing. It answers true,
  ;; or a report of everything wrong with the map.
  (let [answer (rec/probe Heist fields)]
    (when-not (true? answer)
      (let [{:keys [missing undeclared failed]} answer]
        (-> []
            ;; :missing holds the required fields the map lacks.
            (into (map #(str (name %) " is required")) (sort missing))
            ;; :undeclared holds the keys a Heist does not have, such as a misspelt field.
            (into (map #(str (name %) " is not a field of a heist")) (sort undeclared))
            ;; :failed maps each failed check to its failure, whose :doc is the check's own
            ;; docstring: the rule, in the words of the Heist's definition. A check that
            ;; failed because it read an absent field is left out, since the field is
            ;; already reported as required.
            (into (for [[_ {:keys [doc data]}] (sort-by key failed)
                        :when (not (:absent data))]
                    (str "check failed: " doc))))))))
