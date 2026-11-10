;; extra: a concern after an input clause's waits: an input clause runs no check, and takes no flags.
;; expect {:report [{:at [11 12] :level :error :names "on input clause user of collection-write"
;;                   :kondo "::permission on input clause user of collection-write: an input clause takes no concern or :override; they go after a check's waits"}]
;;         :cold :same}
(ns extra.e56-flag-on-input-clause (:require [recognitum.core :as rec]))
(rec/defconcern permission "Checks on the acting user's rights.")
(rec/defchecks collection-write [user]
  rec/checks (may-write [] (some? user)))
(rec/defproven-in Card [owner]
  collection-write
  (user [] ::permission owner)
  rec/checks (owned [] (some? owner)))
