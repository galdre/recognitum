;; usage: the app.dashboard namespace of the example program.
;; expect {:report []}
(ns app.dashboard
  (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))

;; helpers the checks use
(defn non-blank? [s] (and (string? s) (some? (re-find #"\S" s))))

(rec/defproven-in Dashboard [id title collection-id ^:optional acting-user]
  perms/collection-write
  (user          [] acting-user)
  (collection-id [] collection-id)
  rec/checks
  (title [] (non-blank? title))
  (perms/may-write [perms/collection-exists] :override ; keeps the id and the concern
    "dashboards also allow the collection's curators"
    (db/can-curate? acting-user (rec/fetch db/collections collection-id))))
