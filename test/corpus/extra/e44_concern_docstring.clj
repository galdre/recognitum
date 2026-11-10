;; extra: a concern's docstring, under clj-kondo's missing-docstring linter: the var has it, as at run time.
;; expect {:report []
;;         :cold :same}
(ns extra.e44-concern-docstring
  {:clj-kondo/config '{:linters {:missing-docstring {:level :warning}}}}
  (:require [recognitum.core :as rec]))
(rec/defconcern permission
  "Checks of the actor's rights.")
