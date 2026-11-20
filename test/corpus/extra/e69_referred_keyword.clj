;; extra: ::name where name is a var the ns form refers from another namespace: a concern, alone or in a set, a bundle, and clojure.core's count. Known from the ns form alone, so cold too; with the cache, the message names the concern's two right spellings. The right spellings, the symbol and the full keyword, are not reported.
;; expect {:report [{:at [22 13] :level :error :names "is not the id of a concern"
;;             :kondo "::permission on moves is not the id of a concern: permission here is the concern app.perms/permission, whose id is :app.perms/permission. Write permission or :app.perms/permission"}
;;                  {:at [23 25] :level :error :names "is not the id of a concern"
;;             :kondo "::permission on counted is not the id of a concern: permission here is the concern app.perms/permission, whose id is :app.perms/permission. Write permission or :app.perms/permission"}
;;                  {:at [24 13] :level :error :names "is not the id of a concern"
;;             :kondo "::cast-into-box on casts is not the id of a concern: cast-into-box here is app.perms/cast-into-box, a var of another namespace, and a keyword flag is a concern's own id. Where app.perms/cast-into-box is a concern, write cast-into-box or :app.perms/cast-into-box"}
;;                  {:at [25 14] :level :error :names "names no concern"
;;             :kondo "::count on counts names no concern that rec/defconcern defines"}]
;;         :cold [{:at [22 13] :level :error :names "is not the id of a concern"
;;           :kondo "::permission on moves is not the id of a concern: permission here is app.perms/permission, a var of another namespace, and a keyword flag is a concern's own id. Where app.perms/permission is a concern, write permission or :app.perms/permission"}
;;                {:at [23 25] :level :error :names "is not the id of a concern"
;;           :kondo "::permission on counted is not the id of a concern: permission here is app.perms/permission, a var of another namespace, and a keyword flag is a concern's own id. Where app.perms/permission is a concern, write permission or :app.perms/permission"}
;;                {:at [24 13] :level :error :names "is not the id of a concern"
;;           :kondo "::cast-into-box on casts is not the id of a concern: cast-into-box here is app.perms/cast-into-box, a var of another namespace, and a keyword flag is a concern's own id. Where app.perms/cast-into-box is a concern, write cast-into-box or :app.perms/cast-into-box"}
;;                {:at [25 14] :level :error :names "names no concern"
;;           :kondo "::count on counts names no concern that rec/defconcern defines"}]}
(ns extra.e69-referred-keyword (:require [recognitum.core :as rec] [app.perms :as perms :refer [permission cast-into-box]]))
(rec/defconcern audit "Checks an auditor reads.")
(rec/defproven-in Ballot [voter]
  rec/checks
  (moves [] ::permission (some? voter))
  (counted [] #{::audit ::permission} (some? voter))
  (casts [] ::cast-into-box (some? voter))
  (counts [] ::count (some? voter))
  (fine [] #{permission :app.perms/permission ::audit audit} (some? voter)))
