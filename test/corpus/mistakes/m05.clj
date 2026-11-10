;; mistake 5: an input clause naming an input the bundle does not have.
;; expect {:report [{:at [10 4] :level :error :names "usr"
;;                   :kondo "bundle perms/collection-write has no input usr"}
;;                  {:at [9 3] :level :error :names "user"
;;                   :kondo "no clause binds input user of bundle perms/collection-write"}]
;;         :cold []}
(ns mistakes.m05 (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Card [id collection-id ^:optional acting-user]
  perms/collection-write
  (usr           [] acting-user)
  (collection-id [] collection-id))
