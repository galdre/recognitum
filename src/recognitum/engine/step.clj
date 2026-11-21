(ns recognitum.engine.step
  "What every way of running an engine shares:

  - `Engine`, which `recognitum.engine/define` makes;
  - [[step]], which runs a check's body or a continuation to its next park, or to its end;
  - [[failure-of]], which reads the failure data of a signal: the exception that a read of an
    absent field or a failed read of a source throws inside a body;
  - [[nothing-failed]], the result of a run in which nothing failed."
  (:require
   [recognitum.engine.runtime :as rt])
  (:import
   [recognitum.engine.runtime Park]))

;; `ids` holds the check ids in wait order; `fns`, `waits` and `dependents` hold, by position in
;; `ids`, each check's body and int arrays of the positions it waits on and that wait on it.
;; `plans` holds the plans for the last eight assumed sets; `(aget cursor 0)` is the index of
;; the newest.
(deftype Engine [ids fns waits dependents ^objects plans ^ints cursor])

(defn failure-of
  "The failure data for `e`, an exception that a body let escape: `{:absent k}` for a read of
  an absent field, `{:fetch-failed source :cause t}` for a failed read of a source, and nil
  for any other exception."
  [^Exception e]
  (let [d (ex-data e)]
    (cond (contains? d :recognitum.checks/absent)       {:absent (:recognitum.checks/absent d)}
          (contains? d :recognitum.checks/fetch-failed) {:fetch-failed (:recognitum.checks/fetch-failed d)
                                                         :cause (.getCause e)}
          :else                                         nil)))

(deftype Failed [data])

(defn step
  "Runs `(f x)`, where `f` is a body or a continuation, through any trampoline. Returns a Park
  where the body stops at a read of a source, `:recognitum.engine/passed` where it returns
  exactly `true`, and otherwise a `Failed` that holds the failure data: what the body returned,
  or what [[failure-of]] reads of a signal. Rethrows any other exception."
  [f x]
  (try (let [r (rt/settle (f x))]
         (cond (instance? Park r) r
               (true? r)          :recognitum.engine/passed
               :else              (Failed. r)))
       (catch Exception e
         (if-let [d (failure-of e)] (Failed. d) (throw e)))))

(def nothing-failed {:failed {} :blocked #{}})
