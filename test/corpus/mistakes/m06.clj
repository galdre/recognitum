;; mistake 6: an input clause naming a field the type does not have.
;; expect {:report [{:at [8 21] :level :error :names "cst-by"
;;                   :kondo "Unresolved symbol: cst-by"}]
;;         :cold :same}
(ns mistakes.m06 (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven-in Ballot [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (voter         [] cst-by)
  (ballot-box-id [] ballot-box-id))
