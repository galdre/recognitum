;; usage: the app.ballot namespace of the example program.
;; expect {:report []}
(ns app.ballot
  (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))

;; helpers the checks use
(defn non-blank? [s] (and (string? s) (some? (re-find #"\S" s))))

(rec/defproven-in Ballot [id choice ballot-box-id spoiled
                          ^:optional cast-by
                          ^:optional stored-ballot-box-id            ; on update: where the ballot is now
                          ^:optional stored-spoiled]

  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)

  ^{:when-extant stored-ballot-box-id}                               ; skipped on create
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

  (moves-only-where-allowed [perms/may-cast perms/stored-may-cast] ::perms/permission ; bundle checks
    "a move needs the right to cast into both ballot boxes"
    true)

  (officer-active [perms/box-exists]
    "the ballot box's officer is active"
    (let [box (rec/fetch db/ballot-boxes ballot-box-id)]
      (:active? (rec/fetch db/officers (:officer-id box))))))        ; a read keyed by a read
