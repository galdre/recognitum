;; mistake 13: a rec/defcopy map that leaves out a check of the bundle.
;; expect {:report [{:at [7 3] :level :error :names "box-exists"
;;                   :kondo "no new name for check box-exists of bundle perms/cast-into-box"}]
;;         :cold []}
(ns mistakes.m13a (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defcopy half-cast-into-box perms/cast-into-box
  {may-cast half-may-cast})
