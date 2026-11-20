;; extra: a check whose whole body is a concern: its symbol, its id, a set holding one, after a docstring, after a flag, after :override, in a bundle's check; and ::permission, alone or in a set, where permission is a concern this namespace refers. A concern of another namespace as the whole body is reported only where the cache knows it for a concern. An input clause's one form is the input's value, and is not reported.
;; expect {:report [{:at [43 36] :level :error :names "has flags and no body"
;;             :kondo "audit, the whole body of costed, is a flag, so costed has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (costed [] audit \"...\" body)"}
;;                  {:at [48 13] :level :error :names "has flags and no body"
;;             :kondo "shop, the whole body of named, is a flag, so named has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (named [] shop body)"}
;;                  {:at [49 16] :level :error :names "has flags and no body"
;;             :kondo "::audit, the whole body of labelled, is a flag, so labelled has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (labelled [] ::audit body)"}
;;                  {:at [50 14] :level :error :names "has flags and no body"
;;             :kondo "#{1 shop}, the whole body of priced, is a flag, so priced has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (priced [] #{1 shop} body)"}
;;                  {:at [51 28] :level :error :names "has flags and no body"
;;             :kondo "shop, the whole body of sold, is a flag, so sold has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (sold [] shop \"...\" body)"}
;;                  {:at [52 17] :level :error :names "has flags and no body"
;;             :kondo "audit, the whole body of kept, is a flag, so kept has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (kept [] #{audit shop} body)"}
;;                  {:at [53 57] :level :error :names "has flags and no body"
;;             :kondo "shop, the whole body of extra.e72-concern-as-whole-body/counted, is a flag, so extra.e72-concern-as-whole-body/counted has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (extra.e72-concern-as-whole-body/counted [] #{:override shop} body)"}
;;                  {:at [54 13] :level :error :names "is not the id of a concern"
;;             :kondo "::permission on moved is not the id of a concern: permission here is the concern app.perms/permission, whose id is :app.perms/permission. Write permission or :app.perms/permission"}
;;                  {:at [55 42] :level :error :names "is not the id of a concern"
;;             :kondo "::permission on allowed is not the id of a concern: permission here is the concern app.perms/permission, whose id is :app.perms/permission. Write permission or :app.perms/permission"}
;;                  {:at [56 12] :level :error :names "has flags and no body"
;;             :kondo "app.perms/permission, the whole body of sent, is a flag, so sent has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (sent [] app.perms/permission body)"}
;;                  {:at [57 13] :level :error :names "has flags and no body"
;;             :kondo ":app.perms/permission, the whole body of filed, is a flag, so filed has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (filed [] :app.perms/permission body)"}]
;;         :cold [{:at [43 36] :level :error :names "has flags and no body"
;;           :kondo "audit, the whole body of costed, is a flag, so costed has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (costed [] audit \"...\" body)"}
;;                {:at [48 13] :level :error :names "has flags and no body"
;;           :kondo "shop, the whole body of named, is a flag, so named has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (named [] shop body)"}
;;                {:at [49 16] :level :error :names "has flags and no body"
;;           :kondo "::audit, the whole body of labelled, is a flag, so labelled has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (labelled [] ::audit body)"}
;;                {:at [50 14] :level :error :names "has flags and no body"
;;           :kondo "#{1 shop}, the whole body of priced, is a flag, so priced has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (priced [] #{1 shop} body)"}
;;                {:at [51 28] :level :error :names "has flags and no body"
;;           :kondo "shop, the whole body of sold, is a flag, so sold has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (sold [] shop \"...\" body)"}
;;                {:at [52 17] :level :error :names "has flags and no body"
;;           :kondo "audit, the whole body of kept, is a flag, so kept has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (kept [] #{audit shop} body)"}
;;                {:at [53 57] :level :error :names "has flags and no body"
;;           :kondo "shop, the whole body of extra.e72-concern-as-whole-body/counted, is a flag, so extra.e72-concern-as-whole-body/counted has flags and no body: a concern after a clause's waits is one of its flags, and the body follows the flags, as in (extra.e72-concern-as-whole-body/counted [] #{:override shop} body)"}]}
(ns extra.e72-concern-as-whole-body (:require [recognitum.core :as rec] [app.perms :refer [permission]]))
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
  (extra.e72-concern-as-whole-body/counted [] :override shop)
  (moved [] ::permission)
  (allowed [] "the seller may sell it" #{::permission})
  (sent [] app.perms/permission)
  (filed [] :app.perms/permission))
