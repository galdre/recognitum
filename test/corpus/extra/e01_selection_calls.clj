;; extra: selections and functions at call sites, with three arity errors.
;; expect {:report [{:at [25 4] :level :error :names "->Ballot"
;;                   :kondo "app.ballot/->Ballot is called with 2 args but expects 7"}
;;                  {:at [26 4] :level :error :names "seal"
;;                   :kondo "recognitum.core/seal is called with 3 args but expects 1 or 2"}
;;                  {:at [27 4] :level :error :names "proves?"
;;                   :kondo "recognitum.core/proves? is called with 1 arg but expects 2"}]
;;         :cold [{:at [26 4] :level :error :names "seal"
;;                 :kondo "recognitum.core/seal is called with 3 args but expects 1 or 2"}
;;                {:at [27 4] :level :error :names "proves?"
;;                 :kondo "recognitum.core/proves? is called with 1 arg but expects 2"}]}
(ns extra.e01-selection-calls
  (:require [recognitum.core :as rec] [app.ballot :as ballot] [app.perms :as perms] [app.db :as db]))

(defn ok [c]
  [(ballot/->Ballot 1 "n" 2 false nil nil nil)
   (ballot/map->Ballot {})
   (rec/seal c (rec/union rec/shape (rec/reading ::ballot/choice) (rec/fetching db/ballot-boxes)))
   (rec/seal c (rec/except rec/every :app.perms/permission perms/cast-into-box))
   (rec/proven-concerns c)
   (rec/proves? c perms/permission)
   (rec/checks-of rec/every app.ballot.Ballot)])

(defn bad [c]
  [(ballot/->Ballot 1 2)
   (rec/seal c rec/every :extra)
   (rec/proves? c)])
