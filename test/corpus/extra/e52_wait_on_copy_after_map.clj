;; extra: a type binds a copy with a form after its map and waits on a check of it: the hook
;; reports that form, and not the wait.
;; expect {:report [{:at [13 3] :level :error :names "defcopy"
;;                   :kondo "rec/defcopy takes a map {check new-check ...} after the bundle, and nothing after it"}]
;;         :cold :same}
(ns extra.e52-wait-on-copy-after-map (:require [recognitum.core :as rec]))
(rec/defchecks base [u]
  rec/checks
  (base-ok []
    (some? u)))
(rec/defcopy stray base
  {base-ok stray-ok}
  :stray)
(rec/defproven Stray [a]
  stray
  (u [] a)
  rec/checks
  (waits-on-copy [extra.e52-wait-on-copy-after-map/stray-ok]
    true))
