;; extra: as extra/e63/source.clj, in a .cljc file: its marker vars reach other .cljc namespaces through the cache too.
;; expect {:report []
;;         :outline [shop shop--rec-concern plain potion potion--rec-input--cost potion--rec-input--label potion--rec-check--costed potion--rec-check--labelled costed labelled stocked stocked--rec-input--cost stocked--rec-input--label stocked--rec-check--stocked-costed stocked--rec-check--stocked-labelled stocked-costed stocked-labelled unseen unseen--rec-input--anything unseen--rec-check--seen-k seen-k Potion ->Potion map->Potion]
;;         :cold :same}
(ns extra.e64.source (:require [recognitum.core :as rec] [extra.e64.bundle :as bundle]))
(rec/defconcern shop "What the shop needs before it sells a potion.")
(defn plain "Not a concern." [x] x)
(rec/defchecks potion [cost label]
  rec/checks
  (costed [] (some? cost))
  (labelled [] (string? label)))
(rec/defcopy stocked potion {costed stocked-costed labelled stocked-labelled})
(rec/defcopy unseen bundle/stock {k seen-k})
(rec/defproven-in Potion [cost label]
  potion
  (cost [] cost)
  (label [] label)
  rec/checks
  (sold [] shop (some? cost)))
