;; usage: a binding gated on an optional field that none of its input clauses reads.
;; expect {:report [] :cold :same}
(ns app.gated-ballot (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defproven Ballot [id ballot-box-id ^:optional cast-by ^:optional stored-spoiled]
  ^{:when-extant stored-spoiled}
  perms/cast-into-stored-box
  (voter         [] cast-by)
  (ballot-box-id [] ballot-box-id))
