;; extra: rec/fetch in an input clause. An input clause is not a check body: it reads fields only.
;; expect {:report [{:at [7 21] :level :error :names "rec/fetch"
;;                   :kondo "rec/fetch is allowed only inside a check body"}] :cold :same}
(ns extra.e07-fetch-in-input-clause (:require [recognitum.core :as rec] [app.perms :as perms] [app.db :as db]))
(rec/defproven-in Card [id collection-id ^:optional acting-user]
  perms/collection-write
  (user          [] (rec/fetch db/users acting-user))
  (collection-id [] collection-id))
