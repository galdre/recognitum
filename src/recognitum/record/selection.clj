(ns recognitum.record.selection
  "What a selection asks of a type: the checks it selects, the presence checks of the required
  fields among them, the required fields whose presence it asks, whether it selects nothing,
  and the refusal of a seal by a selection that selects nothing."
  (:require
   [clojure.set :as set]
   [clojure.string :as str]
   [recognitum.select :as select]))

(defn- presence
  "The id that stands for the presence check of the required field `f`, a check with no name
  of its own."
  [f]
  [:recognitum.record/present f])

(defn- selected
  "The checks of `type` that `sel` selects, the presence checks of its required fields among
  them. A presence check has no name, is a shape check of its field, reads no source and reads
  its field alone, so a selection selects it as it would any check of that kind."
  [type sel]
  (let [required (:required type)
        op (when (map? sel) (::select/op sel))]
    (case op
      (:every :shape :pure) (into (select/select type sel) (map presence) required)
      :reading (cond-> (select/select type sel) (contains? required (:key sel)) (conj (presence (:key sel))))
      :union (into #{} (mapcat #(selected type %)) (:xs sel))
      :except (reduce set/difference (selected type (:s sel)) (map #(selected type %) (:xs sel)))
      (select/select type sel))))

(defn- asked*
  "The required fields of `type` whose presence `sel` asks: those whose presence check `sel`
  selects, and those that a check `sel` selects, or a check that one waits on, reads. Every
  check waits on the presence check of each required field it reads."
  [type sel]
  (let [required (:required type)
        s (selected type sel)]
    (into (into #{} (keep #(when (vector? %) (second %))) s)
          (comp (mapcat #(get-in type [:by-id % :reads])) (filter required))
          (select/closure type (remove vector? s)))))

(defn asked
  "[[asked*]] as a vector, kept per type and selection while the type's cache has room."
  [type sel]
  (if (= select/every sel)
    (:recognitum.record/required-v type)
    (let [^java.util.concurrent.ConcurrentHashMap kept (:recognitum.record/asked type)]
      (or (.get kept sel)
          (let [a (vec (sort-by str (asked* type sel)))]
            (when (< (.size kept) 1000) (.putIfAbsent kept sel a))
            a)))))

(defn nothing?
  "Whether `sel` selects no check of `type` and asks the presence of none of its required
  fields, kept per type and selection while the type's cache has room."
  [type sel]
  (let [^java.util.concurrent.ConcurrentHashMap kept (:recognitum.record/nothing type)
        b (when (some? sel) (.get kept sel))]
    (if (some? b)
      b
      (let [b (empty? (selected type sel))]
        (when (< (.size kept) 1000) (.putIfAbsent kept sel b))
        b))))

(defn refused-for?
  "Whether a seal by `sel` of a value of the unsealed `type` is refused for its selection: `sel`
  is not every and selects nothing in `type`."
  [type sel]
  (and (not= select/every sel) (nothing? type sel)))

(defn- show-selection
  "`sel` as a caller writes it."
  [sel]
  (cond (keyword? sel) (str sel)
        (instance? recognitum.select.Concern sel) (str (:id sel))
        (= :check (:recognitum/kind sel)) (str (:id sel))
        (= :bundle (:recognitum/kind sel)) (str (:name sel))
        :else (case (::select/op sel)
                :every "rec/every"
                :shape "rec/shape"
                :pure "rec/pure"
                :reading (str "(rec/reading " (:key sel) ")")
                :except (str "(rec/except " (str/join " " (map show-selection (cons (:s sel) (:xs sel)))) ")")
                :union (str "(rec/union" (apply str (map #(str " " (show-selection %)) (:xs sel))) ")")
                (pr-str sel))))

(defn selects-nothing-refusal
  "The refusal of a seal by `sel` of a value of the unsealed `type`, in which `sel` selects
  nothing."
  [type sel]
  (let [tname (:name type)
        t (name tname)
        shown (show-selection sel)
        concern (cond (instance? recognitum.select.Concern sel) (:id sel)
                      (keyword? sel) (when (instance? recognitum.select.Concern (select/named sel)) sel))]
    (ex-info (str tname " has no check that "
                  (if concern
                    (str "carries " concern)
                    (str shown " selects, and no required field whose presence it asks"))
                  ", so a seal by it would prove nothing. If a check of " t " should carry it, give that"
                  " check its flag after its waits. If " t " has nothing to prove for it, give " t
                  " a check that carries it and passes"
                  (when concern
                    (str ", as in (nothing-to-prove [] " concern " \"Why " t " has nothing to prove.\" true)")))
             {:error :recognitum/selects-nothing :type tname :selection sel})))

(defn absent-of
  "The fields of `ask`, a vector, that `data` does not hold, or nil where it holds each."
  [ask data]
  (let [^clojure.lang.IPersistentVector ask ask
        n (.count ask)]
    (loop [i 0]
      (cond (== i n) nil
            (contains? data (.nth ask i)) (recur (inc i))
            :else (into #{} (remove #(contains? data %)) ask)))))
