;; usage: the app.tally namespace of the example program.
;; expect {:report []}
(ns app.tally
  (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))

;; helpers the checks use
(defn non-blank? [s] (and (string? s) (some? (re-find #"\S" s))))

(rec/defproven-in Tally [id label ballot-box-id ^:optional counted-by]
  perms/cast-into-box
  (voter         [] counted-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (label [] (non-blank? label))
  (perms/may-cast [perms/box-exists] :override ; keeps the id and the concern
    "tallies also allow the ballot box's tellers"
    (db/can-tally? counted-by (rec/fetch db/ballot-boxes ballot-box-id))))
