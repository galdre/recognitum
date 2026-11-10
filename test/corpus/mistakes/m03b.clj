;; mistake 3: a misspelled concern on a clause, the concern in another namespace.
;; expect {:report [{:at [9 16] :level :warning :names "perms/permision"
;;                   :kondo "Unresolved var: perms/permision"}]
;;         :cold []}
(ns mistakes.m03b (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Ballot [id ballot-box-id ^:optional cast-by]
  rec/checks
  (ballot-box-id [] (pos-int? ballot-box-id))
  (may-read [] ::perms/permision (some? cast-by)))
