;; mistake 13: a rec/defcopy map that names a check the bundle lacks.
;; expect {:report [{:at [10 4] :level :error :names "may-cst"
;;                   :kondo "bundle perms/cast-into-box has no check may-cst"}
;;                  {:at [9 3] :level :error :names "may-cast"
;;                   :kondo "no new name for check may-cast of bundle perms/cast-into-box"}]
;;         :cold []}
(ns mistakes.m13b (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defcopy other-cast-into-box perms/cast-into-box
  {box-exists other-box-exists
   may-cst    other-may-cast})
