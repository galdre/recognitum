;; mistake 3: a misspelled concern on a clause, the concern in another namespace.
;; expect {:report [{:at [9 16] :level :warning :names "perms/permision"
;;                   :kondo "Unresolved var: perms/permision"}]
;;         :cold []}
(ns mistakes.m03b (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Card [id collection-id ^:optional acting-user]
  rec/checks
  (collection-id [] (pos-int? collection-id))
  (may-read [] ::perms/permision (some? acting-user)))
