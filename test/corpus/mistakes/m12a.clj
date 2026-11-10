;; mistake 12: :override on a misspelled bundle check.
;; expect {:report [{:at [11 4] :level :error :names "perms/may-wrte"
;;                   :kondo "perms/may-wrte is not a check of any bundle bound here"}]
;;         :cold []}
(ns mistakes.m12a (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Dashboard [id collection-id ^:optional acting-user]
  perms/collection-write
  (user          [] acting-user)
  (collection-id [] collection-id)
  rec/checks
  (perms/may-wrte [] :override true))
