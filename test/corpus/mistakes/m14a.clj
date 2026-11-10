;; mistake 14: ^{:when-extant f} naming a field the type does not have.
;; expect {:report [{:at [7 18] :level :error :names "stored-ballot-box"
;;                   :kondo "stored-ballot-box is not a field of this type"}]
;;         :cold :same}
(ns mistakes.m14a (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Ballot [id ballot-box-id ^:optional cast-by ^:optional stored-ballot-box-id]
  ^{:when-extant stored-ballot-box}
  perms/cast-into-stored-box
  (voter         [] cast-by)
  (ballot-box-id [] stored-ballot-box-id))
