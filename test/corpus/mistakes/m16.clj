;; mistake 16: a bundle bound twice in one type.
;; expect {:report [{:at [10 3] :level :error :names "perms/cast-into-box"
;;                   :kondo "bundle perms/cast-into-box is bound twice in this type"}]
;;         :cold :same}
(ns mistakes.m16 (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven Ballot [id ballot-box-id ^:optional cast-by ^:optional stored-ballot-box-id]
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] stored-ballot-box-id))
