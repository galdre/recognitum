;; extra: a copy of a bundle from another namespace. Clean warm and cold.
;; expect {:report [] :cold :same}
(ns extra.e03.copier (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defcopy stored-cast-into-box perms/cast-into-box
  {box-exists stored-box-exists
   may-cast   stored-may-cast})
