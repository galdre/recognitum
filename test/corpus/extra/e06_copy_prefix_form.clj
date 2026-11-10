;; extra: the old :prefix form of rec/defcopy: the hook reports the argument where the map
;; belongs.
;; expect {:report [{:at [7 62] :level :error :names "defcopy"
;;                   :kondo "rec/defcopy takes a map {check new-check ...} after the bundle, and nothing after it"}]
;;         :cold :same}
(ns extra.e06-copy-prefix-form (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defcopy current-collection-write perms/collection-write :prefix current-)
