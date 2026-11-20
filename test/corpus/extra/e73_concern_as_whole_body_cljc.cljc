;; extra: as extra/e72, in a .cljc file.
;; expect {:report [{:at [42 97] :level :warning :names "#'app.perms/permission is referred but never used"
;;             :kondo "#'app.perms/permission is referred but never used"}
;;                  {:at [47 36] :level :error :names "has flags and no body"
;;             :kondo "audit, the whole body of costed, is a flag, so costed has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (costed [] audit \"...\" body)"}
;;                  {:at [52 13] :level :error :names "has flags and no body"
;;             :kondo "shop, the whole body of named, is a flag, so named has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (named [] shop body)"}
;;                  {:at [53 16] :level :error :names "has flags and no body"
;;             :kondo "::audit, the whole body of labelled, is a flag, so labelled has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (labelled [] ::audit body)"}
;;                  {:at [54 14] :level :error :names "has flags and no body"
;;             :kondo "#{1 shop}, the whole body of priced, is a flag, so priced has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (priced [] #{1 shop} body)"}
;;                  {:at [55 28] :level :error :names "has flags and no body"
;;             :kondo "shop, the whole body of sold, is a flag, so sold has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (sold [] shop \"...\" body)"}
;;                  {:at [56 17] :level :error :names "has flags and no body"
;;             :kondo "audit, the whole body of kept, is a flag, so kept has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (kept [] #{audit shop} body)"}
;;                  {:at [57 62] :level :error :names "has flags and no body"
;;             :kondo "shop, the whole body of extra.e73-concern-as-whole-body-cljc/counted, is a flag, so extra.e73-concern-as-whole-body-cljc/counted has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (extra.e73-concern-as-whole-body-cljc/counted [] #{:override shop} body)"}
;;                  {:at [58 13] :level :error :names "is not the id of a concern"
;;             :kondo "::permission on moved is not the id of a concern: permission here is the concern app.perms/permission, whose id is :app.perms/permission. Write permission or :app.perms/permission"}
;;                  {:at [59 42] :level :error :names "is not the id of a concern"
;;             :kondo "::permission on allowed is not the id of a concern: permission here is the concern app.perms/permission, whose id is :app.perms/permission. Write permission or :app.perms/permission"}
;;                  {:at [60 12] :level :error :names "has flags and no body"
;;             :kondo "app.perms/permission, the whole body of sent, is a flag, so sent has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (sent [] app.perms/permission body)"}
;;                  {:at [61 13] :level :error :names "has flags and no body"
;;             :kondo ":app.perms/permission, the whole body of filed, is a flag, so filed has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (filed [] :app.perms/permission body)"}]
;;         :cold [{:at [42 97] :level :warning :names "#'app.perms/permission is referred but never used"
;;           :kondo "#'app.perms/permission is referred but never used"}
;;                {:at [47 36] :level :error :names "has flags and no body"
;;           :kondo "audit, the whole body of costed, is a flag, so costed has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (costed [] audit \"...\" body)"}
;;                {:at [52 13] :level :error :names "has flags and no body"
;;           :kondo "shop, the whole body of named, is a flag, so named has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (named [] shop body)"}
;;                {:at [53 16] :level :error :names "has flags and no body"
;;           :kondo "::audit, the whole body of labelled, is a flag, so labelled has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (labelled [] ::audit body)"}
;;                {:at [54 14] :level :error :names "has flags and no body"
;;           :kondo "#{1 shop}, the whole body of priced, is a flag, so priced has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (priced [] #{1 shop} body)"}
;;                {:at [55 28] :level :error :names "has flags and no body"
;;           :kondo "shop, the whole body of sold, is a flag, so sold has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (sold [] shop \"...\" body)"}
;;                {:at [56 17] :level :error :names "has flags and no body"
;;           :kondo "audit, the whole body of kept, is a flag, so kept has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (kept [] #{audit shop} body)"}
;;                {:at [57 62] :level :error :names "has flags and no body"
;;           :kondo "shop, the whole body of extra.e73-concern-as-whole-body-cljc/counted, is a flag, so extra.e73-concern-as-whole-body-cljc/counted has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (extra.e73-concern-as-whole-body-cljc/counted [] #{:override shop} body)"}]}
(ns extra.e73-concern-as-whole-body-cljc (:require [recognitum.core :as rec] [app.perms :refer [permission]]))
(rec/defconcern audit "Checks an auditor reads.")
(rec/defconcern shop "What the shop needs before it sells a potion.")
(rec/defchecks potion-checks [cost]
  rec/checks
  (costed [] "a potion has a cost" audit)
  (counted [] (some? cost)))
(rec/defproven-in Potion [label cost]
  potion-checks (cost [] shop)
  rec/checks
  (named [] shop)
  (labelled [] ::audit)
  (priced [] #{shop 1})
  (sold [] "a sold potion" shop)
  (kept [] shop audit)
  (extra.e73-concern-as-whole-body-cljc/counted [] :override shop)
  (moved [] ::permission)
  (allowed [] "the seller may sell it" #{::permission})
  (sent [] app.perms/permission)
  (filed [] :app.perms/permission))
