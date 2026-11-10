;; extra: a bundle's docstring, written after its name, under clj-kondo's missing-docstring linter: the bundle's var and its check's var have theirs, as at run time.
;; expect {:report []
;;         :cold :same
;;         :docs {schedule "The checks of a schedule." cron-is-text "each schedule is a string"}}
(ns extra.e48-bundle-docstring
  {:clj-kondo/config '{:linters {:missing-docstring {:level :warning}}}}
  (:require [recognitum.core :as rec]))
(rec/defchecks schedule "The checks of a schedule."
  [crons]
  rec/checks
  (cron-is-text []
    "each schedule is a string"
    (every? string? crons)))
