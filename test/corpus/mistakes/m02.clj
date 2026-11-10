;; mistake 2: a misspelled bundle check in a wait vector.
;; expect {:report [{:at [11 11] :level :warning :names "perms/may-cst"
;;                   :kondo "Unresolved var: perms/may-cst"}]
;;         :cold []}
(ns mistakes.m02 (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Ballot [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (moves [perms/may-cst] true))
