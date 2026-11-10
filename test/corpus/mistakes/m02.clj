;; mistake 2: a misspelled bundle check in a wait vector.
;; expect {:report [{:at [11 11] :level :warning :names "perms/may-wrte"
;;                   :kondo "Unresolved var: perms/may-wrte"}]
;;         :cold []}
(ns mistakes.m02 (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Card [id collection-id ^:optional acting-user]
  perms/collection-write
  (user          [] acting-user)
  (collection-id [] collection-id)
  rec/checks
  (moves [perms/may-wrte] true))
