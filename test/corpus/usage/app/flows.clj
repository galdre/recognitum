;; usage: the app.flows namespace of the example program.
;; clojure.set is required, for `missing`.
;; expect {:report []}
(ns app.flows
  (:require [recognitum.core :as rec] [app.ballot :as ballot] [app.tally :as tally]
            [app.contexts :refer [importing]] [app.perms :as perms] [clojure.set]))

;; helpers the checks use
(defn store! [x] x)

(defn import-all [{:keys [ballots tallies]}]                         ; construction checks nothing
  (concat (map #(rec/seal (ballot/map->Ballot %) importing) ballots)
          (map #(rec/seal (tally/map->Tally %) importing) tallies)))

(defn create-ballot [row voter]
  (-> (ballot/map->Ballot row) (assoc ::ballot/cast-by voter) (rec/seal rec/every)))

(defn change-choice [b new-choice]
  (-> b (assoc ::ballot/choice new-choice) (rec/seal rec/every)))    ; reruns choice only

(defn revalidate! [ballots]
  (rec/check-all ballots rec/pure))                                  ; no source is called

(defn after-permission-change! [ballots tallies]
  (rec/check-all (concat ballots tallies) perms/may-cast))           ; one id in both types

(defn publish! [x]
  {:pre [(rec/proves? x rec/every)]}
  (store! x))

(defn missing [c]                                                    ; for an error message
  (clojure.set/difference (rec/checks-of rec/every c) (rec/proven-checks c)))
