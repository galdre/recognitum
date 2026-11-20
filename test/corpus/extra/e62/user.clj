;; extra: copies of the copies of extra.e62.copier, under the missing-docstring linter: that a check has a docstring passes through a copy in another namespace, one namespace at a time.
;; expect {:report []
;;         :kondo [{:at [12 91] :level :warning :kondo "Missing docstring."}]
;;         :cache-from ["extra/e62/source.clj" "extra/e62/copier.clj"]
;;         :cold [{:at [12 91] :level :warning :kondo "Missing docstring."}
;;                {:at [13 91] :level :warning :kondo "Missing docstring."}]
;;         :docs {daily-cron-is-text "each schedule is a string"}
;;         :kondo-docs {daily-cron-is-text nil}}
(ns extra.e62.user
  {:clj-kondo/config '{:linters {:missing-docstring {:level :warning}}}}
  (:require [recognitum.core :as rec] [extra.e62.copier :as copier]))
(rec/defcopy yearly "A copy of a copy of undocumented." copier/weekly {weekly-cron-is-set yearly-cron-is-set})
(rec/defcopy daily "A copy of a copy of documented." copier/nightly {nightly-cron-is-text daily-cron-is-text})
