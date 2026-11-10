;; mistake 14: ^{:when-extant f} naming a required field.
;; expect {:report [{:at [7 18] :level :error :names "collection-id"
;;                   :kondo "collection-id is a required field: :when-extant never skips"}]
;;         :cold :same}
(ns mistakes.m14b (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Card [id collection-id ^:optional acting-user ^:optional stored-collection-id]
  ^{:when-extant collection-id}
  perms/current-collection-write
  (user          [] acting-user)
  (collection-id [] collection-id))
