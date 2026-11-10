;; mistake 12: :override on a check of a bundle that is not bound here (only its copy is).
;; expect {:report [{:at [11 4] :level :error :names "perms/may-cast"
;;                   :kondo "perms/may-cast is not a check of any bundle bound here"}]
;;         :cold []}
(ns mistakes.m12b (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Tally [id ballot-box-id ^:optional cast-by]
  perms/cast-into-stored-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (perms/may-cast [] :override true))
