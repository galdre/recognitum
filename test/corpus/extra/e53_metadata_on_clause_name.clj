;; extra: metadata on a clause's name: the macros read none there, and refuse it.
;; expect {:report [{:at [8 16] :level :error :names "the name of never"
;;                   :kondo "^::permission on the name of never: a clause takes no metadata; its concerns and :override go after its waits, as in (never [waits] ::permission body)"}]
;;         :cold :same}
(ns extra.e53-metadata-on-clause-name (:require [recognitum.core :as rec]))
(rec/defconcern permission "Checks on the voter's rights.")
(rec/defproven-in Ballot [id]
  rec/checks (^::permission never [] (= id :never)))
