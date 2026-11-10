;; extra: metadata on a clause: the macros read none there, and refuse it.
;; expect {:report [{:at [8 15] :level :error :names "on the clause never"
;;                   :kondo "^::permission on the clause never: a clause takes no metadata; its concerns and :override go after its waits, as in (never [waits] ::permission body)"}]
;;         :cold :same}
(ns extra.e58-metadata-on-clause (:require [recognitum.core :as rec]))
(rec/defconcern permission "Checks on the voter's rights.")
(rec/defproven-in Ballot [id]
  rec/checks ^::permission (never [] (= id :never)))
