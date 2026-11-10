;; extra: a user macro in a check body, and reads inside threading and let forms.
;; expect {:report [] :cold :same}
(ns extra.e09-body-macros (:require [recognitum.core :as rec] [app.db :as db]))
(defmacro unless-blank [s & body] `(if (seq ~s) (do ~@body) false))
(rec/defproven Note [title ballot-box-id]
  rec/checks
  (title [] (unless-blank title (string? title)))
  (box-on-file []
    (-> (rec/fetch db/ballot-boxes ballot-box-id) some?))
  (officer-known []
    (let [c (rec/fetch db/ballot-boxes ballot-box-id)
          u (rec/fetch db/officers (:officer-id c))]
      (some? u))))
