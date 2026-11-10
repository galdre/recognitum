;; mistake 17: waits that form a cycle among the checks of a bundle.
;; expect {:report [{:at [8 4] :level :error :names "box-exists"
;;                   :kondo "the waits form a cycle: box-exists -> may-cast -> box-exists"}]
;;         :cold :same}
(ns mistakes.m17b (:require [recognitum.core :as rec] [app.db :as db]))
(rec/defchecks cast-into-box [voter ballot-box-id]
  rec/checks
  (box-exists [may-cast] (some? (rec/fetch db/ballot-boxes ballot-box-id)))
  (may-cast [box-exists] (db/can-cast? voter (rec/fetch db/ballot-boxes ballot-box-id))))
