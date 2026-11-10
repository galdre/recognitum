;; extra: a copy's docstring, written after its name: the copy's var has it, under clj-kondo as at run time.
;; expect {:report []
;;         :cold :same
;;         :docs {nightly "The checks of a nightly schedule."}}
(ns extra.e49-copy-docstring (:require [recognitum.core :as rec]))
(rec/defchecks schedule [crons]
  rec/checks
  (cron-is-text []
    "each schedule is a string"
    (every? string? crons)))
(rec/defcopy nightly "The checks of a nightly schedule."
  schedule
  {cron-is-text nightly-cron-is-text})
