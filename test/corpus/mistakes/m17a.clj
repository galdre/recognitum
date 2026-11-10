;; mistake 17: waits that form a cycle, through a bundle check the type overrides.
;; expect {:report [{:at [11 4] :level :error :names "moves"
;;                   :kondo "the waits form a cycle: moves -> perms/may-cast -> moves"}]
;;         :cold :same}
(ns mistakes.m17a (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven Ballot [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (moves [perms/may-cast] true)
  (perms/may-cast [moves] :override true))
