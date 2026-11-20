;; extra: a bundle that extra.e63.source copies. Linted alone with extra.e63.source in the cache, the copy cannot see it, and so its inputs are unknown.
;; expect {:report []
;;         :outline [stock stock--rec-input--anything stock--rec-check--k k]
;;         :cold :same}
(ns extra.e63.bundle (:require [recognitum.core :as rec]))
(rec/defchecks stock [anything] rec/checks (k [] (some? anything)))
