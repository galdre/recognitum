;; extra: a bare wait that names a bundle check this namespace defines.
;; expect {:report [{:at [11 17] :level :error :names "titled"
;;                   :kondo "titled is not a check of this type. A wait on a bundle's check is qualified: extra.e20-wait-names-bundle-check/titled"}]
;;         :cold :same}
(ns extra.e20-wait-names-bundle-check (:require [recognitum.core :as rec]))
(rec/defchecks named [label]
  rec/checks (titled [] (string? label)))
(rec/defproven Note [title]
  named (label [] title)
  rec/checks
  (short-title [titled] (< (count title) 80)))
