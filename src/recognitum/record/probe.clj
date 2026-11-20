(ns recognitum.record.probe
  "A probe: [[probe-all]] and [[probe]] run a type's checks on plain maps, in one run of the
  engine, with some sources answered by overrides, and make no draft and write no memory. A
  check's read of a source calls [[sourced]] of it, which answers the probe's override where the
  probe running the check gives one; a run that starts outside a probe, or inside a check body,
  sees no override ([[run-all-plain]]). Hidden: the dynamic var that holds a probe's overrides,
  which nothing outside this namespace binds or reads."
  (:require
   [clojure.set :as set]
   [recognitum.proof :as proof]
   [recognitum.record.draft :refer [draft?]]
   [recognitum.record.reports :refer [answer engine-passed]]
   [recognitum.record.selection :refer [absent-of asked]]
   [recognitum.record.types :refer [current? type-of-class]]
   [recognitum.select :as select])
  (:import
   [recognitum.record.draft Draft]))

(def ^:dynamic ^:private *overrides*
  "The overrides of the probe whose checks run on this thread: a map from a source to the
  function that answers in its place. Nil outside a probe. A run that reads a source rebinds it
  to nil, even one that a check body starts inside a probe."
  nil)

(defn sourced
  "The function a check's read of `src` calls: `src`, or the override the probe running the
  check gave for it. The define layer writes every `(&fetch src k)` and `(&fetch-each src ks)`
  of a check body as a read of `(sourced src)`."
  [src]
  (let [o *overrides*]
    (if (nil? o) src (get o src src))))

(defn run-all-plain
  "`(run-all items)` with no probe's overrides in force: a run started inside a probe's check
  body reads its sources themselves."
  [run-all items]
  (if (nil? *overrides*)
    (run-all items)
    (binding [*overrides* nil] (run-all items))))

;;; ------------------------------------------------------------------ probing

(defn- probe-type!
  "The type whose class is `c`, a current definition; refuses anything else."
  [c]
  (let [t (when (class? c) (type-of-class c))]
    (when-not t
      (throw (ex-info (str "probe takes a type's class: " (pr-str c))
                      {:error :recognitum/not-a-type :value c})))
    (when-not (current? t)
      (throw (ex-info (str (:name t) " was redefined: this class is of an earlier definition. Probe the"
                           " class that " (name (:name t)) " names now in " (namespace (:name t)))
                      {:error :recognitum/displaced-constructor :type (:name t)})))
    t))

(defn- entries
  "The entries of map `m`, a draft, a value of any type or any other map, as a plain map; its
  memory, where it has one, is not read."
  [m]
  (cond (draft? m) (.-data ^Draft m)
        (map? m)   (proof/plain-map m)
        :else      (throw (ex-info (str "probe reads a map: " (pr-str m))
                                   {:error :recognitum/not-a-map :value m}))))

(defn probe-all
  "For each map of `field-maps`, what [[check]] with `sel` answers of a fresh draft of the type
  whose class is `c` holding its entries, with the keys the type does not declare under
  `:undeclared`: true, or a report. One run of the engine over every map, in which each read
  of a source that `overrides` maps calls its override in its place. Makes no draft and writes
  no memory."
  [c field-maps sel overrides]
  (let [type (probe-type! c)
        picked (select/select type sel)
        to-run (select/closure type picked)
        assumed (set/difference (:ids type) to-run)
        ask (asked type sel)
        datas (mapv entries field-maps)
        engine (:engine type)
        jobs (mapv (fn [d] [engine d assumed]) datas)
        o (not-empty overrides)
        results (if (and (nil? o) (nil? *overrides*))
                  ((:run-all type) jobs)
                  (binding [*overrides* o] ((:run-all type) jobs)))
        declared (:keys type)]
    (mapv (fn [d result]
            (let [r (answer type result sel picked to-run (absent-of ask d))
                  u (not-empty (into #{} (remove #(contains? declared %)) (keys d)))]
              (cond (nil? u)  r
                    (true? r) (assoc engine-passed :undeclared u)
                    :else     (assoc r :undeclared u))))
          datas (vec results))))

(defn probe
  "What [[probe-all]] answers of the one map `fields`."
  [c fields sel overrides]
  (nth (probe-all c [fields] sel overrides) 0))
