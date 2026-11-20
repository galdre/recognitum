;; extra: a copy's checks, under clj-kondo's missing-docstring linter, in the file of the bundles: each has its docstring exactly when the copied check has one, as at run time, through a copy of a copy too. The undocumented checks warn, at their new names, and only they: in one copy, a documented check's copy does not hide the warning of an undocumented one.
;; expect {:report []
;;         :kondo [{:at [15 1] :level :warning :kondo "Missing docstring."}
;;                 {:at [20 1] :level :warning :kondo "Missing docstring."}
;;                 {:at [25 73] :level :warning :kondo "Missing docstring."}
;;                 {:at [29 23] :level :warning :kondo "Missing docstring."}
;;                 {:at [30 84] :level :warning :kondo "Missing docstring."}]
;;         :cold :same
;;         :docs {nightly-cron-is-text "each schedule is a \"cron\" string,\n    read in UTC, a back\\slash\tand a tab"
;;                hourly-cron-is-text "each schedule is a \"cron\" string,\n    read in UTC, a back\\slash\tand a tab"
;;                daily-text-given "each schedule is a \"cron\" string,\n    read in UTC, a back\\slash\tand a tab"}}
(ns extra.e61-copy-check-docstring
  {:clj-kondo/config '{:linters {:missing-docstring {:level :warning}}}}
  (:require [recognitum.core :as rec]))
(rec/defchecks undocumented "Checks without docstrings." [crons] rec/checks (cron-is-set [] (set? crons)))
(rec/defchecks documented "Checks with docstrings." [crons]
  rec/checks
  (cron-is-text [] "each schedule is a \"cron\" string,
    read in UTC, a back\\slash\tand a tab" (every? string? crons)))
(rec/defchecks mixed "One check with a docstring, one without." [crons]
  rec/checks
  (text-given [] "each schedule is a \"cron\" string,
    read in UTC, a back\\slash\tand a tab" (every? string? crons))
  (set-given [] (set? crons)))
(rec/defcopy weekly "A copy of undocumented." undocumented {cron-is-set weekly-cron-is-set})
(rec/defcopy nightly "A copy of documented." documented {cron-is-text nightly-cron-is-text})
(rec/defcopy hourly "A copy of a copy of documented." nightly {nightly-cron-is-text hourly-cron-is-text})
(rec/defcopy monthly "A copy of a copy of undocumented." weekly
  {weekly-cron-is-set monthly-cron-is-set})
(rec/defcopy daily "A copy of mixed." mixed {text-given daily-text-given set-given daily-set-given})
