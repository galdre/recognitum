;; mistake 12: :override on a check of a bundle that is not bound here (only its copy is).
;; expect {:report [{:at [11 4] :level :error :names "perms/may-write"
;;                   :kondo "perms/may-write is not a check of any bundle bound here"}]
;;         :cold []}
(ns mistakes.m12b (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Dashboard [id collection-id ^:optional acting-user]
  perms/current-collection-write
  (user          [] acting-user)
  (collection-id [] collection-id)
  rec/checks
  (perms/may-write [] :override true))
