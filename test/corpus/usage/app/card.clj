;; usage: the app.card namespace of the example program.
;; expect {:report []}
(ns app.card
  (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))

;; helpers the checks use
(defn non-blank? [s] (and (string? s) (some? (re-find #"\S" s))))

(rec/defproven-in Card [id name collection-id archived
                        ^:optional acting-user
                        ^:optional stored-collection-id              ; on update: where the card is now
                        ^:optional stored-archived]

  perms/collection-write
  (user          [] acting-user)
  (collection-id [] collection-id)

  ^{:when-extant stored-collection-id}                               ; skipped on create
  perms/current-collection-write
  (user          [] acting-user)
  (collection-id [] stored-collection-id)

  rec/checks
  (name          [] (non-blank? name))
  (collection-id [] (pos-int? collection-id))
  (archived      [] (boolean? archived))

  (not-archived-on-edit []
    "an archived card is not edited"
    (or (not (rec/extant? stored-archived)) (not stored-archived)))

  (moves-only-where-allowed [perms/may-write perms/current-may-write] ::perms/permission ; bundle checks
    "a move needs write access to both collections"
    true)

  (owner-active [perms/collection-exists]
    "the collection's owner is active"
    (let [coll (rec/fetch db/collections collection-id)]
      (:active? (rec/fetch db/users (:owner-id coll))))))            ; a read keyed by a read
