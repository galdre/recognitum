;; extra: a concern after an input clause's waits: an input clause runs no check, and takes no flags.
;; expect {:report [{:at [11 13] :level :error :names "on input clause voter of cast-into-box"
;;                   :kondo "::permission on input clause voter of cast-into-box: an input clause takes no concern or :override; they go after a check's waits"}]
;;         :cold :same}
(ns extra.e56-flag-on-input-clause (:require [recognitum.core :as rec]))
(rec/defconcern permission "Checks on the voter's rights.")
(rec/defchecks cast-into-box [voter]
  rec/checks (may-cast [] (some? voter)))
(rec/defproven-in Ballot [owner]
  cast-into-box
  (voter [] ::permission owner)
  rec/checks (owned [] (some? owner)))
