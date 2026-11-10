;; mistake 3: a misspelled concern on a clause, the concern in the same namespace.
;; expect {:report [{:at [9 16] :level :error :names "permision"
;;                   :kondo "Unresolved symbol: permision"}]
;;         :cold :same}
(ns mistakes.m03a (:require [recognitum.core :as rec] [app.db :as db]))
(rec/defconcern permission "Checks on the voter's rights.")
(rec/defchecks cast-into-box [voter ballot-box-id]
  rec/checks
  (may-cast [] ::permision (db/can-cast? voter ballot-box-id)))
