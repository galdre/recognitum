;; extra: ::name where name is a concern that :refer :all brings in: the hook knows it only from the cache; cold, clj-kondo cannot resolve the name. The right spellings are not reported.
;; expect {:report [{:at [10 96] :level :warning :names "use alias or "
;;             :kondo "use alias or :refer [permission]"}
;;                  {:at [13 13] :level :error :names "is not the id of a concern"
;;             :kondo "::permission on moves is not the id of a concern: permission here is the concern app.perms/permission, whose id is :app.perms/permission. Write permission or :app.perms/permission"}]
;;         :cold [{:at [10 96] :level :warning :names "use alias or "
;;           :kondo "use alias or :refer"}
;;                {:at [13 13] :level :error :names "Unresolved symbol"
;;           :kondo "Unresolved symbol: permission"}]}
(ns extra.e71-referred-keyword-refer-all (:require [recognitum.core :as rec] [app.perms :refer :all]))
(rec/defproven-in Ballot [voter]
  rec/checks
  (moves [] ::permission (some? voter))
  (fine [] #{permission :app.perms/permission} (some? voter)))
