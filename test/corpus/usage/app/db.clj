;; usage: a source of the usage program (a stub for app.db).
;; expect {:report []}
(ns app.db)
(def ballot-boxes "a source" nil)
(def officers "a source" nil)
(defn can-cast? [_voter _box])
(defn can-tally? [_voter _box])
