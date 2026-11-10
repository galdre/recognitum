;; extra: a documented rec/defcopy with a form after its map: the hook reports that form.
;; expect {:report [{:at [8 3] :level :error :names "defcopy"
;;                   :kondo "rec/defcopy takes a map {check new-check ...} after the bundle, and nothing after it"}]
;;         :cold :same}
(ns extra.e50-copy-after-map (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defcopy cast-into-stored-box "A copy with a stray form."
  perms/cast-into-box {box-exists stored-exists may-cast stored-may-cast}
  :stray)
