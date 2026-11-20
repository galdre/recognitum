;; extra: copies of bundles of extra.e62.source, and a copy of each copy, under the missing-docstring linter. When the cache holds the source, a copy of a documented check has no docstring under clj-kondo, as the cache holds none, and is not reported for it; a copy of an undocumented check is, at its new name. The mark silences only that warning: a copied check that redefines a var still warns of it. Cold, the hook cannot see the source and every copied check warns.
;; expect {:report []
;;         :kondo [{:at [24 80] :level :warning :kondo "Missing docstring."}
;;                 {:at [27 85] :level :warning :kondo "Missing docstring."}
;;                 {:at [28 91] :level :warning :kondo "Missing docstring."}
;;                 {:at [29 118] :level :warning :kondo "redefined var #'extra.e62.copier/taken"}]
;;         :cache-from ["extra/e62/source.clj"]
;;         :cold [{:at [24 80] :level :warning :kondo "Missing docstring."}
;;                {:at [25 78] :level :warning :kondo "Missing docstring."}
;;                {:at [26 85] :level :warning :kondo "Missing docstring."}
;;                {:at [27 85] :level :warning :kondo "Missing docstring."}
;;                {:at [28 64] :level :warning :kondo "Missing docstring."}
;;                {:at [28 91] :level :warning :kondo "Missing docstring."}
;;                {:at [29 118] :level :warning :kondo "Missing docstring."}
;;                {:at [29 118] :level :warning :kondo "redefined var #'extra.e62.copier/taken"}]
;;         :docs {nightly-cron-is-text "each schedule is a string"
;;                hourly-cron-is-text "each schedule is a string"}
;;         :kondo-docs {nightly-cron-is-text nil
;;                      hourly-cron-is-text nil}}
(ns extra.e62.copier
  {:clj-kondo/config '{:linters {:missing-docstring {:level :warning}}}}
  (:require [recognitum.core :as rec] [extra.e62.source :as source]))
(def taken "A var that a copied check redefines." nil)
(rec/defcopy weekly "A copy of undocumented." source/undocumented {cron-is-set weekly-cron-is-set})
(rec/defcopy nightly "A copy of documented." source/documented {cron-is-text nightly-cron-is-text})
(rec/defcopy hourly "A copy of a copy of documented." nightly {nightly-cron-is-text hourly-cron-is-text})
(rec/defcopy monthly "A copy of a copy of undocumented." weekly {weekly-cron-is-set monthly-cron-is-set})
(rec/defcopy daily "A copy of mixed." source/mixed {text-given daily-text-given set-given daily-set-given})
(rec/defcopy again "A copy of documented, whose check takes a name already defined." source/documented {cron-is-text taken})
