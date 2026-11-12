;; extra: a symbol after a clause's waits, with more forms after it, that names no concern: a misspelled
;; concern, a bundle's check, a field, or a plain var, which the hook knows only from its cache.
;; expect {:report [{:at [25 13] :level :error :names "shpo"
;;                   :kondo "Unresolved symbol: shpo"}
;;                  {:at [26 12] :level :error :names "costed"
;;                   :kondo "costed is not a concern: no rec/defconcern defines it"}
;;                  {:at [27 16] :level :error :names "label"
;;                   :kondo "Unresolved symbol: label"}
;;                  {:at [28 14] :level :error :names "priced?"
;;                   :kondo "priced? is not a concern: no rec/defconcern defines it"}]
;;         :cold [{:at [25 13] :level :error :names "shpo"
;;                 :kondo "Unresolved symbol: shpo"}
;;                {:at [26 12] :level :error :names "costed"
;;                 :kondo "costed is not a concern: no rec/defconcern defines it"}
;;                {:at [27 16] :level :error :names "label"
;;                 :kondo "Unresolved symbol: label"}]}
(ns extra.e60-symbol-not-a-concern (:require [recognitum.core :as rec]))
(rec/defconcern shop "What the shop needs before it sells a potion.")
(defn priced? [cost] (pos? cost))
(rec/defchecks potion-checks [cost]
  rec/checks (costed [] (some? cost)))
(rec/defproven-in Potion [label cost]
  potion-checks (cost [] cost)
  rec/checks
  (named [] shpo (string? label))
  (sold [] costed "a bundle's check" (some? cost))
  (labelled [] label (some? label))
  (priced [] priced? (priced? cost)))
