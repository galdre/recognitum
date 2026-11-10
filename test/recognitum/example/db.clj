(ns recognitum.example.db
  "In-memory tables that stand in for a database, read through sources that log their calls.")

(defonce calls (atom []))

(def ^:private tables
  {:ballot-boxes {1 {:officer-id 10 :voters #{"ann"} :tellers #{}}
                  2 {:officer-id 11 :voters #{"bob"} :tellers #{"cy"}}
                  3 {:officer-id 12 :voters #{"ann" "bob"} :tellers #{}}}
   :officers {10 {:active? true} 11 {:active? true} 12 {:active? false}}})

(defn- source [table]
  (fn [ks]
    (swap! calls conj [table ks])
    (select-keys (tables table) ks)))

(def ballot-boxes "A source: ballot box id to ballot box." (source :ballot-boxes))
(def officers "A source: officer id to officer." (source :officers))

(defn can-cast? [voter box] (contains? (:voters box) voter))
(defn can-tally? [voter box] (contains? (:tellers box) voter))
