;; extra: a concern keyword on a clause that names a var no rec/defconcern defines.
;; expect {:report [{:at [12 16] :level :error :names "collection-exists"
;;                   :kondo "collection-exists is not a concern: no rec/defconcern defines it"}
;;                  {:at [16 13] :level :error :names "perms/may-write"
;;                   :kondo "perms/may-write is not a concern: no rec/defconcern defines it"}]
;;         :cold [{:at [12 16] :level :error :names "collection-exists"
;;                 :kondo "collection-exists is not a concern: no rec/defconcern defines it"}]}
(ns extra.e05-concern-not-a-concern (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))
(rec/defchecks collection-read [user collection-id]
  rec/checks
  (collection-exists [] (some? collection-id))
  (may-read [] ::collection-exists (db/can-write? user collection-id)))
(rec/defproven-in Card [id collection-id]
  rec/checks
  (collection-id [] (pos-int? collection-id))
  (moves [] ::perms/may-write true))
