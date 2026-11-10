;; extra: a check's docstring, under clj-kondo's missing-docstring linter: the check's var has it, as at run time. The bundle's docstring is metadata, so that the check is the form's only var under test.
;; expect {:report []
;;         :cold :same}
(ns extra.e45-check-docstring
  {:clj-kondo/config '{:linters {:missing-docstring {:level :warning}}}}
  (:require [recognitum.core :as rec]))
(rec/defchecks ^{:doc "The checks of a schedule."} schedule [crons]
  rec/checks
  (cron-is-text []
    "each schedule is a string"
    (every? string? crons)))
