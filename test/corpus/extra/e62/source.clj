;; extra: bundles that extra.e62.copier copies: one whose check has a docstring, one whose check has none, and one with a check of each kind.
;; expect {:report []
;;         :kondo [{:at [7 1] :level :warning :kondo "Missing docstring."}
;;                 {:at [11 1] :level :warning :kondo "Missing docstring."}]
;;         :cold :same}
(ns extra.e62.source {:clj-kondo/config '{:linters {:missing-docstring {:level :warning}}}} (:require [recognitum.core :as rec]))
(rec/defchecks undocumented "Checks without docstrings." [crons] rec/checks (cron-is-set [] (set? crons)))
(rec/defchecks documented "Checks with docstrings." [crons]
  rec/checks
  (cron-is-text [] "each schedule is a string" (every? string? crons)))
(rec/defchecks mixed "One check with a docstring, one without." [crons]
  rec/checks
  (text-given [] "each schedule is a string" (every? string? crons))
  (set-given [] (set? crons)))
