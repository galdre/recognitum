;; mistake 12: :override on a name that is a concern, not a check.
;; expect {:report [{:at [11 4] :level :error :names "perms/permission"
;;                   :kondo "perms/permission is not a check of any bundle bound here"}]
;;         :cold []}
(ns mistakes.m12c (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Tally [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (perms/permission [] :override true))
