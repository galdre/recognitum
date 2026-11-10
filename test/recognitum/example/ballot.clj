(ns recognitum.example.ballot
  "The ballot and tally of the example application, as types whose constructors run every
  check."
  (:require
   [clojure.string :as str]
   [recognitum.core :as rec]
   [recognitum.example.db :as db]
   [recognitum.example.perms :as perms]))

(defn non-blank? [s] (and (string? s) (not (str/blank? s))))

(rec/defproven Ballot [id choice ballot-box-id spoiled
                       ^:optional cast-by
                       ^:optional stored-ballot-box-id
                       ^:optional stored-spoiled]

  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)

  ^{:when-extant stored-ballot-box-id}
  perms/cast-into-stored-box
  (voter         [] cast-by)
  (ballot-box-id [] stored-ballot-box-id)

  rec/checks
  (choice        [] (non-blank? choice))
  (ballot-box-id [] (pos-int? ballot-box-id))
  (spoiled       [] (boolean? spoiled))

  (not-spoiled-on-edit []
    "a spoiled ballot is not edited"
    (or (not (rec/extant? stored-spoiled)) (not stored-spoiled)))

  (moves-only-where-allowed [perms/may-cast perms/stored-may-cast] ::perms/permission
    "a move needs the right to cast into both ballot boxes"
    true)

  (officer-active [perms/box-exists]
    "the ballot box's officer is active"
    (let [box (rec/fetch db/ballot-boxes ballot-box-id)]
      (true? (:active? (rec/fetch db/officers (:officer-id box)))))))

(rec/defproven Tally [id label ballot-box-id ^:optional counted-by]
  perms/cast-into-box
  (voter         [] counted-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (label [] (non-blank? label))
  (perms/may-cast [perms/box-exists] :override
    "tallies also allow the ballot box's tellers"
    (let [box (rec/fetch db/ballot-boxes ballot-box-id)]
      (or (db/can-cast? counted-by box) (db/can-tally? counted-by box)))))
