;; extra: a flag that is neither :override nor a concern, and :override in a bundle.
;; expect {:report [{:at [9 24] :level :error :names "unknown flag :permission on never"
;;                   :kondo "unknown flag :permission on never: a clause's flags are :override and concerns"}
;;                  {:at [11 25] :level :error :names "a bundle's check replaces no check"
;;                   :kondo ":override on always: a bundle's check replaces no check; :override is for a clause of a type that replaces a check of a bound bundle"}]
;;         :cold :same}
(ns extra.e57-unknown-flag (:require [recognitum.core :as rec]))
(rec/defproven-in Ballot [id]
  rec/checks (never [] :permission (= id :never)))
(rec/defchecks ballot-checks [id]
  rec/checks (always [] :override (some? id)))
