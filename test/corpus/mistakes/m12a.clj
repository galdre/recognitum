;; mistake 12: :override on a misspelled bundle check.
;; expect {:report [{:at [11 4] :level :error :names "perms/may-cst"
;;                   :kondo "perms/may-cst is not a check of any bundle bound here"}]
;;         :cold []}
(ns mistakes.m12a (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Tally [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (perms/may-cst [] :override true))
