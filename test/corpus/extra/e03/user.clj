;; extra: a type that binds the copy from extra.e03.copier and waits on a copied check.
;; expect {:report [] :cold :same}
(ns extra.e03.user (:require [recognitum.core :as rec] [extra.e03.copier :as copier]))
(rec/defproven-in Thing [id ballot-box-id ^:optional cast-by]
  copier/stored-cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  rec/checks
  (ok [copier/stored-may-cast] true))
