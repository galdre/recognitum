;; mistake 4: a misspelled concern var in a selection.
;; expect {:report [{:at [7 25] :level :warning :names "perms/permision"
;;                   :kondo "Unresolved var: perms/permision"}]
;;         :cold []}
(ns mistakes.m04 (:require [recognitum.core :as rec] [app.perms :as perms]))
(rec/defcontext importing "doc"
  (rec/except rec/every perms/permision))
