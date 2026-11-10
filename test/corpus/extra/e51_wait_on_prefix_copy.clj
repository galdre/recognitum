;; extra: a type binds a copy written in the old :prefix form and waits on a check of it: the
;; hook reports the copy's form, and not the wait, whose check it cannot know.
;; expect {:report [{:at [11 28] :level :error :names "defcopy"
;;                   :kondo "rec/defcopy takes a map {check new-check ...} after the bundle, and nothing after it"}]
;;         :cold :same}
(ns extra.e51-wait-on-prefix-copy (:require [recognitum.core :as rec]))
(rec/defchecks base [u]
  rec/checks
  (base-ok []
    (some? u)))
(rec/defcopy prefixed base :prefix prefixed-)
(rec/defproven Prefixed [a]
  prefixed
  (u [] a)
  rec/checks
  (waits-on-copy [extra.e51-wait-on-prefix-copy/prefixed-base-ok]
    true))
