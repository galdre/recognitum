;; mistake 6: an input clause naming a field the type does not have.
;; expect {:report [{:at [8 21] :level :error :names "acting-usr"
;;                   :kondo "Unresolved symbol: acting-usr"}]
;;         :cold :same}
(ns mistakes.m06 (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Card [id collection-id ^:optional acting-user]
  perms/collection-write
  (user          [] acting-usr)
  (collection-id [] collection-id))
