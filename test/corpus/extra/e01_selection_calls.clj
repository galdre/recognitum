;; extra: selections and functions at call sites, with three arity errors.
;; expect {:report [{:at [25 4] :level :error :names "->Card"
;;                   :kondo "app.card/->Card is called with 2 args but expects 7"}
;;                  {:at [26 4] :level :error :names "seal"
;;                   :kondo "recognitum.core/seal is called with 3 args but expects 1 or 2"}
;;                  {:at [27 4] :level :error :names "proves?"
;;                   :kondo "recognitum.core/proves? is called with 1 arg but expects 2"}]
;;         :cold [{:at [26 4] :level :error :names "seal"
;;                 :kondo "recognitum.core/seal is called with 3 args but expects 1 or 2"}
;;                {:at [27 4] :level :error :names "proves?"
;;                 :kondo "recognitum.core/proves? is called with 1 arg but expects 2"}]}
(ns extra.e01-selection-calls
  (:require [recognitum.core :as rec] [app.card :as card] [app.perms :as perms] [app.db :as db]))

(defn ok [c]
  [(card/->Card 1 "n" 2 false nil nil nil)
   (card/map->Card {})
   (rec/seal c (rec/union rec/shape (rec/reading ::card/name) (rec/fetching db/collections)))
   (rec/seal c (rec/except rec/every :app.perms/permission perms/collection-write))
   (rec/proven-concerns c)
   (rec/proves? c perms/permission)
   (rec/checks-of rec/every app.card.Card)])

(defn bad [c]
  [(card/->Card 1 2)
   (rec/seal c rec/every :extra)
   (rec/proves? c)])
