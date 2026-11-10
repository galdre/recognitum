;; extra: metadata on a clause's waits: the macros read none there, and refuse it.
;; expect {:report [{:at [8 22] :level :error :names "the waits of never"
;;                   :kondo "^::permission on the waits of never: a clause takes no metadata; its concerns and :override go after its waits, as in (never [waits] ::permission body)"}]
;;         :cold :same}
(ns extra.e54-metadata-on-waits (:require [recognitum.core :as rec]))
(rec/defconcern permission "Checks on the acting user's rights.")
(rec/defchecks card-checks [id]
  rec/checks (never ^::permission [] (= id :never)))
