;; extra: a flag out of a clause's flags' place: after a docstring (a symbol, a keyword, a set), a second bare flag, a flag after :override, in a bundle's check and in an input clause. A concern of another namespace written so is reported only where the cache knows it for a concern. A keyword as the last form of a longer body is the body, and is not reported.
;; expect {:report [{:at [39 36] :level :error :names "where no flag is read"
;;             :kondo "audit, written after the docstring of costed, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (costed [] audit \"...\" ...)"}
;;                  {:at [42 37] :level :error :names "where no flag is read"
;;             :kondo "::shop, written after the docstring of input clause cost of potion-checks, is in the body, where no flag is read: an input clause takes no concern or :override; they go after a check's waits"}
;;                  {:at [44 36] :level :error :names "where no flag is read"
;;             :kondo "shop, written after the docstring of named, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (named [] shop \"...\" ...)"}
;;                  {:at [45 34] :level :error :names "where no flag is read"
;;             :kondo "::audit, written after the docstring of labelled, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (labelled [] ::audit \"...\" ...)"}
;;                  {:at [46 36] :level :error :names "where no flag is read"
;;             :kondo "#{audit shop}, written after the docstring of priced, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (priced [] #{audit shop} \"...\" ...)"}
;;                  {:at [47 17] :level :error :names "where no flag is read"
;;             :kondo "audit, written after shop on sold, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (sold [] #{audit shop} ...)"}
;;                  {:at [48 50] :level :error :names "where no flag is read"
;;             :kondo "shop, written after :override on extra.e67-misplaced-flag/counted, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (extra.e67-misplaced-flag/counted [] #{:override shop} ...)"}
;;                  {:at [49 40] :level :error :names "where no flag is read"
;;             :kondo "app.perms/permission, written after the docstring of allowed, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (allowed [] app.perms/permission \"...\" ...)"}
;;                  {:at [50 38] :level :error :names "where no flag is read"
;;             :kondo "permission, written after the docstring of moved, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (moved [] permission \"...\" ...)"}]
;;         :cold [{:at [39 36] :level :error :names "where no flag is read"
;;           :kondo "audit, written after the docstring of costed, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (costed [] audit \"...\" ...)"}
;;                {:at [42 37] :level :error :names "where no flag is read"
;;           :kondo "::shop, written after the docstring of input clause cost of potion-checks, is in the body, where no flag is read: an input clause takes no concern or :override; they go after a check's waits"}
;;                {:at [44 36] :level :error :names "where no flag is read"
;;           :kondo "shop, written after the docstring of named, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (named [] shop \"...\" ...)"}
;;                {:at [45 34] :level :error :names "where no flag is read"
;;           :kondo "::audit, written after the docstring of labelled, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (labelled [] ::audit \"...\" ...)"}
;;                {:at [46 36] :level :error :names "where no flag is read"
;;           :kondo "#{audit shop}, written after the docstring of priced, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (priced [] #{audit shop} \"...\" ...)"}
;;                {:at [47 17] :level :error :names "where no flag is read"
;;           :kondo "audit, written after shop on sold, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (sold [] #{audit shop} ...)"}
;;                {:at [48 50] :level :error :names "where no flag is read"
;;           :kondo "shop, written after :override on extra.e67-misplaced-flag/counted, is in the body, where no flag is read: a clause's flags follow its waits, before its docstring, and several go in one set, as in (extra.e67-misplaced-flag/counted [] #{:override shop} ...)"}]}
(ns extra.e67-misplaced-flag (:require [recognitum.core :as rec] [app.perms :refer [permission]]))
(rec/defconcern audit "Checks an auditor reads.")
(rec/defconcern shop "What the shop needs before it sells a potion.")
(rec/defchecks potion-checks [cost]
  rec/checks
  (costed [] "a potion has a cost" audit (some? cost))
  (counted [] (some? cost)))
(rec/defproven-in Potion [label cost]
  potion-checks (cost [] "the cost" ::shop cost)
  rec/checks
  (named [] "a potion has a label" shop (string? label))
  (labelled [] "a label is text" ::audit (string? label))
  (priced [] "a price is positive" #{shop audit} (pos? cost))
  (sold [] shop audit (some? cost))
  (extra.e67-misplaced-flag/counted [] :override shop (some? cost))
  (allowed [] "the seller may sell it" app.perms/permission (some? label))
  (moved [] "the seller may move it" permission (some? label))
  (last-form [] (some? label) ::shop))
