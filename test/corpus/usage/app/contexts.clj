;; usage: the app.contexts namespace of the example program.
;; expect {:report []}
(ns app.contexts
  (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))

(rec/defcontext importing
  "Serialization import: no voter; everything else must hold."
  (rec/except rec/every perms/permission))

(rec/defcontext ballot-boxes-down
  "The ballot boxes table is offline."
  (rec/except rec/every (rec/fetching db/ballot-boxes)))
