;; extra: rec/extant? and rec/when-extant inside a fn, a fn literal, a for, a lazy-seq and a delay.
;; expect {:report [] :cold :same}
(ns extra.e66-presence-inside-built-fns (:require [recognitum.core :as rec]))
(rec/defproven Note [^:optional title]
  rec/checks
  (in-fn [] ((fn [] (or (rec/extant? title) (rec/when-extant title true)))))
  (in-literal [] (#(rec/when-extant title (string? title))))
  (in-for [] (every? true? (for [_ [1]] (rec/when-extant title (string? title)))))
  (in-lazy-seq [] (every? true? (lazy-seq (list (rec/when-extant title (string? title))))))
  (in-delay [] @(delay (rec/when-extant title (string? title)))))
