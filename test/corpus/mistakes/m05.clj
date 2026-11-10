;; mistake 5: an input clause naming an input the bundle does not have.
;; expect {:report [{:at [10 4] :level :error :names "votr"
;;                   :kondo "bundle perms/cast-into-box has no input votr"}
;;                  {:at [9 3] :level :error :names "voter"
;;                   :kondo "no clause binds input voter of bundle perms/cast-into-box"}]
;;         :cold []}
(ns mistakes.m05 (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Ballot [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (votr          [] cast-by)
  (ballot-box-id [] ballot-box-id))
