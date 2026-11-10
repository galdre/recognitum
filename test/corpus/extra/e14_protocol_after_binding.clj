;; extra: a protocol after a bundle binding.
;; expect {:report [] :cold :same}
(ns extra.e14-protocol-after-binding (:require [recognitum.core :as rec] [app.perms :as perms]))
(defprotocol Owned (owner [x]))
(rec/defproven Ballot [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id)
  Owned
  (owner [_] cast-by))
