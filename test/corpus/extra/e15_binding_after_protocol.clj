;; extra: a bundle binding after a protocol.
;; expect {:report [{:at [9 3] :level :error :names "perms/cast-into-box"
;;                   :kondo "perms/cast-into-box follows the protocol Owned: the checks sections, rec/checks and the bundle bindings, come before the protocols"}]
;;         :cold :same}
(ns extra.e15-binding-after-protocol (:require [recognitum.core :as rec] [app.perms :as perms]))
(defprotocol Owned (owner [x]))
(rec/defproven Ballot [id ballot-box-id ^:optional cast-by]
  Owned (owner [_] cast-by)
  perms/cast-into-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id))
