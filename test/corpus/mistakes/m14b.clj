;; mistake 14: ^{:when-extant f} naming a required field.
;; expect {:report [{:at [7 18] :level :error :names "ballot-box-id"
;;                   :kondo "ballot-box-id is a required field: :when-extant never skips"}]
;;         :cold :same}
(ns mistakes.m14b (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Ballot [id ballot-box-id ^:optional cast-by ^:optional stored-ballot-box-id]
  ^{:when-extant ballot-box-id}
  perms/cast-into-stored-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id))
