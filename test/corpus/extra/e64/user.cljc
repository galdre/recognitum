;; extra: as extra/e63/user.clj, in .cljc files: what the hook learns of extra.e64.source through the cache alone.
;; expect {:report [{:at [16 33] :level :error :names "labelled"
;;                   :kondo "no new name for check labelled of bundle source/potion"}
;;                  {:at [17 96] :level :error :names "costed"
;;                   :kondo "bundle source/stocked has no check costed"}
;;                  {:at [19 3] :level :error :names "label"
;;                   :kondo "no clause binds input label of bundle source/potion"}
;;                  {:at [21 4] :level :error :names "colour"
;;                   :kondo "bundle source/potion has no input colour"}
;;                  {:at [27 13] :level :error :names "source/plain"
;;                   :kondo "source/plain is not a concern: no rec/defconcern defines it"}]
;;         :cache-from ["extra/e64/source.cljc"]
;;         :outline [part part--rec-input--cost part--rec-input--label part--rec-check--part-costed part-costed again again--rec-input--cost again--rec-input--label again--rec-check--again-x again--rec-check--again-costed again--rec-check--again-labelled again-costed again-labelled again-x Order ->Order map->Order]
;;         :cold []}
(ns extra.e64.user (:require [recognitum.core :as rec] [extra.e64.source :as source]))
(rec/defcopy part source/potion {costed part-costed})
(rec/defcopy again source/stocked {stocked-costed again-costed stocked-labelled again-labelled costed again-x})
(rec/defproven-in Order [cost]
  source/potion
  (cost [] cost)
  (colour [] cost)
  source/unseen
  (anything [] cost)
  rec/checks
  (paid [] source/shop (some? cost))
  (kept [] ::source/shop (some? cost))
  (plain [] source/plain (some? cost)))
