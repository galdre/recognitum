;; usage: the app.perms namespace of the example program.
;; expect {:report []}
(ns app.perms
  (:require [recognitum.core :as rec] [app.db :as db]))

(rec/defconcern permission "Checks on the voter's rights.")

(rec/defchecks cast-into-box [voter ballot-box-id]
  rec/checks
  (box-exists []
    "the ballot box is on file"
    (some? (rec/fetch db/ballot-boxes ballot-box-id)))

  (may-cast [box-exists] ::permission
    "the voter may cast into the ballot box"
    (db/can-cast? voter (rec/fetch db/ballot-boxes ballot-box-id))))   ; voter absent: throws, so fails

(rec/defcopy cast-into-stored-box cast-into-box
  {box-exists stored-box-exists
   may-cast   stored-may-cast})
