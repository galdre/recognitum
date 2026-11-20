;; extra: as extra/e74, in a .cljc file.
;; expect {:report [{:at [5 109] :level :warning :names "#'app.perms/cast-into-box is referred but never used"
;;             :kondo "#'app.perms/cast-into-box is referred but never used"}]
;;         :cold :same}
(ns extra.e75-constant-as-whole-body-cljc (:require [recognitum.core :as rec] [app.perms :refer [permission cast-into-box]]))
(rec/defconcern shop "What the shop needs before it sells a potion.")
(rec/defchecks potion-checks [cost]
  rec/checks
  (counted [] (some? cost)))
(rec/defproven-in Potion [label cost]
  potion-checks (cost [] shop)
  rec/checks
  (named [] ::q)
  (labelled [] :shop)
  (priced [] #{1 :q})
  (sold [] "a sold potion" ::cast-into-box)
  (allowed [] permission (some? label))
  (said [] (str :shop) (some? label)))
