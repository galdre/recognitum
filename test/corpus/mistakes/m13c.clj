;; mistake 13: a rec/defcopy map that names a check twice.
;; expect {:report [{:at [9 4] :level :error :names "may-cast"
;;                   :kondo "may-cast is named twice in the rec/defcopy map"}]
;;         :cold :same}
(ns mistakes.m13c (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defcopy twice-cast-into-box perms/cast-into-box
  {box-exists twice-box-exists
   may-cast   twice-may-cast
   may-cast   twice-may-cast-2})
