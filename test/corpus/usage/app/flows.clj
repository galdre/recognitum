;; usage: the app.flows namespace of the example program.
;; clojure.set is required, for `missing`.
;; expect {:report []}
(ns app.flows
  (:require [recognitum.core :as rec] [app.card :as card] [app.dashboard :as dash]
            [app.contexts :refer [importing]] [app.perms :as perms] [clojure.set]))

;; helpers the checks use
(defn store! [x] x)

(defn import-all [{:keys [cards dashboards]}]                        ; construction checks nothing
  (concat (map #(rec/seal (card/map->Card %) importing) cards)
          (map #(rec/seal (dash/map->Dashboard %) importing) dashboards)))

(defn create-card [row user]
  (-> (card/map->Card row) (assoc ::card/acting-user user) (rec/seal rec/every)))

(defn rename [c new-name]
  (-> c (assoc ::card/name new-name) (rec/seal rec/every)))         ; reruns name only

(defn revalidate! [cards]
  (rec/check-all cards rec/pure))                                    ; no source is called

(defn after-permission-change! [cards dashboards]
  (rec/check-all (concat cards dashboards) perms/may-write))         ; one id in both types

(defn publish! [x]
  {:pre [(rec/proves? x rec/every)]}
  (store! x))

(defn missing [c]                                                    ; for an error message
  (clojure.set/difference (rec/checks-of rec/every c) (rec/proven-checks c)))
