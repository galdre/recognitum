;; extra: rec/fetch in an input clause. An input clause is not a check body: it reads fields only.
;; expect {:report [{:at [7 21] :level :error :names "rec/fetch"
;;                   :kondo "rec/fetch is allowed only inside a check body"}] :cold :same}
(ns extra.e07-fetch-in-input-clause (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))
(rec/defproven-in Ballot [id ballot-box-id ^:optional cast-by]
  perms/cast-into-box
  (voter         [] (rec/fetch db/officers cast-by))
  (ballot-box-id [] ballot-box-id))
