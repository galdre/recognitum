;; extra: a check whose whole body is a constant that is no concern: ::q, :shop, a set of those, and ::cast-into-box, where cast-into-box is a bundle this namespace refers; and a body of two forms whose first is a call holding a keyword. The macros accept each, and nothing is reported.
;; expect {:report []
;;         :cold :same}
(ns extra.e74-constant-as-whole-body (:require [recognitum.core :as rec] [app.perms :refer [permission cast-into-box]]))
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
