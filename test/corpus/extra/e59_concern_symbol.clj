;; extra: a concern named by its symbol after a clause's waits: alone, qualified by an alias, or in a set with a keyword.
;; expect {:report []
;;         :cold :same}
(ns extra.e59-concern-symbol (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))
(rec/defconcern audit "Checks an auditor reads.")
(rec/defchecks box-read [voter ballot-box-id]
  rec/checks
  (box-exists [] audit (some? ballot-box-id))
  (may-read [box-exists] #{perms/permission ::audit} "the voter may read the box"
    (db/can-cast? voter ballot-box-id)))
(rec/defproven-in Ballot [id voter]
  rec/checks
  (moves [] perms/permission (some? voter))
  (counted [] #{audit} "an id is counted" (pos-int? id)))
