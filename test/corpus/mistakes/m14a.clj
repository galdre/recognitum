;; mistake 14: ^{:when-extant f} naming a field the type does not have.
;; expect {:report [{:at [7 18] :level :error :names "stored-collection"
;;                   :kondo "stored-collection is not a field of this type"}]
;;         :cold :same}
(ns mistakes.m14a (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Card [id collection-id ^:optional acting-user ^:optional stored-collection-id]
  ^{:when-extant stored-collection}
  perms/current-collection-write
  (user          [] acting-user)
  (collection-id [] stored-collection-id))
