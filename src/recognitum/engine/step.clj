(ns recognitum.engine.step
  "What every way of running an engine shares: the `Engine` that `recognitum.engine/define`
  makes, and one step of a check's body. [[step]] runs a body or a continuation to its next
  park, to `:recognitum.engine/passed`, or to a `Failed` holding the failure; [[failure-of]]
  reads the failure a signal a body let escape stands for; [[nothing-failed]] is the result of a
  run in which nothing failed."
  (:require
   [recognitum.engine.runtime :as rt])
  (:import
   [recognitum.engine.runtime Park]))

;; `plans` keeps the plans of the last eight assumed sets, the newest at `(aget cursor 0)`
(deftype Engine [ids fns waits dependents ^objects plans ^ints cursor])

(defn failure-of
  "The failure data of a signal `e` a body let escape, or nil when `e` is no signal."
  [^Exception e]
  (let [d (ex-data e)]
    (cond (contains? d :recognitum.checks/absent)       {:absent (:recognitum.checks/absent d)}
          (contains? d :recognitum.checks/fetch-failed) {:fetch-failed (:recognitum.checks/fetch-failed d)
                                                         :cause (.getCause e)}
          :else                                         nil)))

(deftype Failed [data])

(defn step
  "Runs `(f x)`, a body or a continuation, to its next Park, or to `:recognitum.engine/passed` or a Failed.
  Rethrows what the body throws, unless it is a signal."
  [f x]
  (try (let [r (rt/settle (f x))]
         (cond (instance? Park r) r
               (true? r)          :recognitum.engine/passed
               :else              (Failed. r)))
       (catch Exception e
         (if-let [d (failure-of e)] (Failed. d) (throw e)))))

(def nothing-failed {:failed {} :blocked #{}})
