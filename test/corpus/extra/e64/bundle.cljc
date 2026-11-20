;; extra: a bundle that extra.e64.source copies, in a .cljc file; see extra/e63/bundle.clj.
;; expect {:report []
;;         :outline [stock stock--rec-input--anything stock--rec-check--k k]
;;         :cold :same}
(ns extra.e64.bundle (:require [recognitum.core :as rec]))
(rec/defchecks stock [anything] rec/checks (k [] (some? anything)))
