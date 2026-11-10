;; extra: metadata on rec/checks and on a protocol: the macros read none there, and refuse it.
;; expect {:report [{:at [11 4] :level :error :names "on rec/checks"
;;                   :kondo "^::permission on rec/checks: a clause takes no metadata; its concerns and :override go after its waits, as in (name [waits] ::permission body)"}
;;                  {:at [12 4] :level :error :names "on Labelled"
;;                   :kondo "^::permission on Labelled: a clause takes no metadata; its concerns and :override go after its waits, as in (name [waits] ::permission body)"}]
;;         :cold :same}
(ns extra.e55-metadata-on-marker (:require [recognitum.core :as rec]))
(rec/defconcern permission "Checks on the acting user's rights.")
(defprotocol Labelled (label [x]))
(rec/defproven-in Card [id]
  ^::permission rec/checks (never [] (= id :never))
  ^::permission Labelled (label [_] "card"))
