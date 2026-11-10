;; mistake 17: waits that form a cycle, through a wait on a whole bundle.
;; expect {:report [{:at [11 4] :level :error :names "moves"
;;                   :kondo "the waits form a cycle: moves -> perms/cast-into-box -> perms/may-cast -> moves"}]
;;         :cold []}
(ns mistakes.m17c (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven Ballot [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (moves [perms/cast-into-box] true)
  (perms/may-cast [moves] :override true))
