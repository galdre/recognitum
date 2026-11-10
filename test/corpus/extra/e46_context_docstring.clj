;; extra: a context's docstring, under clj-kondo's missing-docstring linter: the var has it, as at run time.
;; expect {:report []
;;         :cold :same}
(ns extra.e46-context-docstring
  {:clj-kondo/config '{:linters {:missing-docstring {:level :warning}}}}
  (:require [recognitum.core :as rec]))
(rec/defcontext importing
  "Serialization import: everything must hold."
  rec/every)
