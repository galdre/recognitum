;; extra: a concern keyword on a clause that names a var no rec/defconcern defines.
;; expect {:report [{:at [12 16] :level :error :names "box-exists"
;;                   :kondo "box-exists is not a concern: no rec/defconcern defines it"}
;;                  {:at [16 13] :level :error :names "perms/may-cast"
;;                   :kondo "perms/may-cast is not a concern: no rec/defconcern defines it"}]
;;         :cold [{:at [12 16] :level :error :names "box-exists"
;;                 :kondo "box-exists is not a concern: no rec/defconcern defines it"}]}
(ns extra.e05-concern-not-a-concern (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))
(rec/defchecks box-read [voter ballot-box-id]
  rec/checks
  (box-exists [] (some? ballot-box-id))
  (may-read [] ::box-exists (db/can-cast? voter ballot-box-id)))
(rec/defproven-in Ballot [id ballot-box-id]
  rec/checks
  (ballot-box-id [] (pos-int? ballot-box-id))
  (moves [] ::perms/may-cast true))
