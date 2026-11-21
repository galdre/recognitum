(ns recognitum.record.probe
  "Probes: [[probe-all]] and [[probe]] run a type's checks on plain maps in one run of the
  engine, with some sources answered by overrides. A probe makes no draft and writes no
  memory.

  A check body's read of a source calls [[sourced]] of the source, which answers the override
  that the running probe gives for it, if any. Every other run goes through
  [[run-all-plain]] and sees no override, even one that a check body starts inside a probe.
  Hidden: the dynamic var that holds a probe's overrides, which nothing outside this
  namespace binds or reads."
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
  function that answers in its place. Nil outside a probe. Every run other than a probe's own
  binds it to nil ([[run-all-plain]]), even one that a check body starts inside a probe."
  nil)

(defn sourced
  "The function a check's read of `src` calls: `src`, or the override the probe running the
  check gave for it. A probe's override reaches only a read written as a read of
  `(sourced src)`; the defining macros write every `(&fetch src k)` and `(&fetch-each src ks)`
  of a check body so."
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
  "The type whose class is `c`. Throws `:recognitum/not-a-type` where `c` is not a type's
  class, and `:recognitum/displaced-constructor` where it is the class of a displaced
  definition."
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
  "The entries of `m`, a draft, a value of any type or any other map, as a plain map; its
  memory, where it has one, is not read. Throws `:recognitum/not-a-map` where `m` is not a
  map."
  [m]
  (cond (draft? m) (.-data ^Draft m)
        (map? m)   (proof/plain-map m)
        :else      (throw (ex-info (str "probe reads a map: " (pr-str m))
                                   {:error :recognitum/not-a-map :value m}))))

(defn probe-all
  "For each map of `field-maps`, what [[recognitum.record.runs/check]] with `sel` answers of a
  new draft of the type whose class is `c` holding the map's entries, true or a report, with
  the keys the type does not declare under `:undeclared` (a report wherever there are any).
  Runs every map in one run of the engine, in which each read of a source that `overrides`
  maps calls its override instead. Makes no draft and writes no memory. Throws
  `:recognitum/not-a-type` where `c` is not a type's class, `:recognitum/displaced-constructor`
  where it is the class of a displaced definition, and `:recognitum/not-a-map` for an element
  of `field-maps` that is not a map."
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
