;; extra: fetch written without rec/ in a namespace that does not refer rec/fetch, so fetch names nothing.
;; expect {:report [{:at [6 38] :level :error :names "fetch" :kondo "Unresolved symbol: fetch"}]
;;         :cold :same}
(ns extra.e11-unresolved-fetch (:require [recognitum.core :as rec] [app.db :as db]))
(rec/defproven Note [title ballot-box-id]
  rec/checks (box-on-file [] (some? (fetch db/ballot-boxes ballot-box-id))))
