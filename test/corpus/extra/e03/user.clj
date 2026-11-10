;; extra: a type that binds the copy from extra.e03.copier and waits on a copied check.
;; expect {:report [] :cold :same}
(ns extra.e03.user (:require [recognitum.core :as rec] [extra.e03.copier :as copier]))
(rec/defproven-in Thing [id collection-id ^:optional acting-user]
  copier/stored-collection-write
  (user          [] acting-user)
  (collection-id [] collection-id)
  rec/checks
  (ok [copier/stored-may-write] true))
