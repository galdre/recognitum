(ns recognitum.record.reports
  "The reports of a run of a type's checks and their messages, the refusals of the record
  layer, and the tests of declared and required keys that the refusals rest on."
  (:require
   [clojure.string :as str]
   [recognitum.select :as select]))

(defn- blocked-by
  "The checks in `blocked` that did not run because `id` failed: those waiting on it, directly
  or through another check in `blocked`."
  [type id blocked]
  (loop [acc #{}]
    (let [more (into acc (filter (fn [b] (some #(or (= id %) (acc %)) (get-in type [:by-id b :waits]))))
                     blocked)]
      (if (= more acc) acc (recur more)))))

(defn pulled-back
  "A map from each check of `ids` that an `except` in `sel` removed, but that ran because a
  check of `to-run` waits on it, to `{:waited-on-by ws :hint h}`: `ws`, the checks of `to-run`
  that wait on it, and `h`, a message that says why it ran."
  [type sel picked to-run ids]
  (let [ex (select/excepted type sel)]
    (into {} (for [id ids
                   :when (and (contains? ex id) (not (contains? picked id)))
                   :let [ws (set (for [w to-run :when (contains? (get-in type [:by-id w :waits]) id)] w))
                         names (str/join ", " (sort ws))]]
               [id {:waited-on-by ws
                    :hint (str id " ran although an except removed it, because " names
                               (if (next ws) " wait" " waits") " on it, and a check runs whenever a"
                               " check that waits on it runs. To leave it out, also remove " names ".")}]))))

(defn report
  "The report of a run: nil where nothing failed or was blocked, else `{:failed :blocked}`, each
  failed check's entry holding its failure `:data`, its `:doc` where it has one, and the
  checks it `:blocked`. `pull`, where given, is a function of the ids that failed or were
  blocked, and its answer, where not empty, goes under `:pulled-back`."
  ([type result] (report type result nil))
  ([type {:keys [failed blocked]} pull]
   (when (or (seq failed) (seq blocked))
     (cond-> {:failed (into {} (for [[id data] failed]
                                 [id (cond-> {:data data :blocked (blocked-by type id blocked)}
                                       (get-in type [:by-id id :doc]) (assoc :doc (get-in type [:by-id id :doc])))]))
              :blocked blocked}
       pull (as-> r (let [pb (pull (concat (keys failed) blocked))]
                      (cond-> r (seq pb) (assoc :pulled-back pb))))))))

(defn- show [x]
  (if (instance? Throwable x)
    (str "#error[" (.getName (class x)) " " (pr-str (ex-message x)) "]")
    (pr-str x)))

(defn- failure-message [type {:keys [failed blocked pulled-back missing]}]
  (str (:name type)
       (when (or (seq failed) (seq blocked) (empty? missing))
         (str " failed " (count failed) (if (= 1 (count failed)) " check" " checks")))
       (when (seq missing)
         (str (when (or (seq failed) (seq blocked)) " and") " lacks the required field"
              (when (next missing) "s") " " (str/join ", " (map pr-str (sort missing)))))
       (when (and (empty? failed) (seq blocked)) (str "; blocked: " (str/join ", " (sort blocked))))
       (apply str (for [[id {:keys [data doc blocked]}] (sort-by key failed)]
                    (str "\n  " id (when doc (str " (" doc ")")) ": " (show data)
                         (when (seq blocked) (str ", which blocked " (str/join ", " (sort blocked)))))))
       (apply str (for [[_ {:keys [hint]}] (sort-by key pulled-back)] (str "\n  " hint)))))

(defn displaced-refusal
  "The refusal of a write to `v`, or of a method called with it, where `v` is a value of the type
  named `tname` and a later definition has displaced the one `v` belongs to."
  [tname v]
  (ex-info (str tname " was redefined: this value is of an earlier definition, so it is not"
                " sealed and refuses writes and its type's methods. To prove it under the current"
                " definition: (rec/seal (rec/draft v))")
           {:error :recognitum/displaced :type tname :value v}))

(defn displaced-unsealed
  "The refusal of a write, a method or a run of checks on `v`, a value of the unsealed type
  named `tname`, where a later definition has displaced the one `v` belongs to."
  [tname v]
  (ex-info (str tname " was redefined: this value is of an earlier definition, so it proves nothing"
                " and refuses writes, its type's methods and every run of checks. To make a value of"
                " the current definition: (" (namespace tname) "/map->" (name tname) " (into {} v))")
           {:error :recognitum/displaced :type tname :value v}))

(defn no-drafts
  "The refusal to open, clean or draft anything of the unsealed type named `tname`."
  [tname]
  (ex-info (str tname " has no drafts: its values check nothing when made or written, and remember"
                " in place what passed. Make one with " (namespace tname) "/map->" (name tname)
                ", and run its checks with rec/check or rec/seal")
           {:error :recognitum/no-drafts :type tname}))

(defn no-definition
  "The refusal to draft `v`, a value of a displaced definition of the type named `tname`, where
  that name no longer names a current definition of the type."
  [tname v]
  (ex-info (str tname " has no current definition: this value is of a displaced definition, and"
                " its name no longer names a definition of the type, so it has no drafts")
           {:error :recognitum/no-current-definition :type tname :value v}))

(defn displaced-constructor
  "The refusal of a constructor of the type named `tname`, held from before a later definition
  displaced the one it makes. `remedy`, if given, says what to call instead of the current
  `map->T`."
  [tname remedy]
  (ex-info (str tname " was redefined: this constructor is of an earlier definition and makes"
                " nothing. "
                (or remedy (str "Call the current " (namespace tname) "/map->" (name tname))))
           {:error :recognitum/displaced-constructor :type tname}))

(defn displaced-draft
  "The refusal to seal a draft of the type named `tname`, opened from the class of a definition
  that a later one displaced."
  [tname]
  (let [n (namespace tname), t (name tname)]
    (ex-info (str tname " was redefined: this draft is of an earlier definition and seals nothing."
                  " Make a value of the current definition with " n "/map->" t ", or seal a draft of"
                  " the class " n " now names " t ": (rec/seal (into (rec/draft " t ") m))")
             {:error :recognitum/displaced-constructor :type tname})))

(defn check-failed
  "The ex-info of the `:recognitum/check-failed` failure of a seal, a constructor or a write of
  `type`. Its data is the report `rep` (an empty report where `rep` is nil), with the required
  fields `absent` under `:missing` where any is, and `:error` and `:type`."
  ([type rep] (check-failed type rep nil))
  ([type rep absent]
   (let [rep (cond-> (or rep {:failed {} :blocked #{}})
               absent (assoc :missing absent))]
     (ex-info (failure-message type rep)
              (assoc rep :error :recognitum/check-failed :type (:name type))))))

(defn refuse-undeclared!
  "Throws `:recognitum/undeclared-keys` where a key of `ks` is one that `type` does not
  declare; where `data` is given, only such a key that `data` holds counts."
  ([type ks] (refuse-undeclared! type ks nil))
  ([type ks data]
   (let [declared (:keys type)
         bad? (fn [k] (and (not (contains? declared k)) (or (nil? data) (contains? data k))))]
     (when (reduce (fn [_ k] (if (bad? k) (reduced true) false)) false ks)
       (let [bad (filter bad? ks)]
         (throw (ex-info (str (:name type) " has no field " (str/join ", " (map pr-str (sort-by str bad)))
                              ". Its fields: " (str/join " " (map :key (:fields type))))
                         {:error :recognitum/undeclared-keys :type (:name type) :keys (set bad)})))))))

(defn all-declared?
  "Whether `declared?` holds of every key of map `m`."
  [declared? m]
  (reduce-kv (fn [_ k _] (if (declared? k) true (reduced false))) true m))

(defn member-of
  "A predicate that answers whether its argument is in the set `xs`. Where `xs` holds a few
  keywords, it compares by identity, which keywords allow because they are interned."
  [xs]
  (if (and (<= (count xs) 16) (every? keyword? xs))
    (let [^objects a (object-array xs)
          n (alength a)]
      (fn [x] (loop [i 0] (cond (== i n) false (identical? x (aget a i)) true :else (recur (inc i))))))
    (fn [x] (contains? xs x))))

(defn missing
  "The set of the required fields of `type` that `data` does not hold, or nil where it holds
  each. A required field's presence is a check of its own, with no name."
  [type data]
  (when-not (reduce (fn [_ k] (if (contains? data k) true (reduced false))) true (:recognitum.record/required-v type))
    (into #{} (remove #(contains? data %)) (:recognitum.record/required-v type))))

(def engine-passed
  "A run's result where nothing failed and nothing was blocked."
  {:failed {} :blocked #{}})

(defn answer
  "What a run of `sel` answers: true, or the report of `result`. Where `absent`, the required
  fields that the value lacks, is not nil, it goes under `:missing`, and the answer is a
  report even where nothing failed."
  ([type result sel picked to-run] (answer type result sel picked to-run nil))
  ([type result sel picked to-run absent]
   (let [r (report type result #(pulled-back type sel picked to-run %))]
     (cond absent (assoc (or r engine-passed) :missing absent)
           r      r
           :else  true))))
