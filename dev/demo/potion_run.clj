(ns demo.potion-run
  "The Potion example end to end: one potion brewed, sold, refused at court, mended and served.
  Each printed line is a form, then what it returned or the error it threw; the lines that
  read the guild also print the calls it received.

      clojure -M:dev -m demo.potion-run"
  (:require
   [demo.guild :as guild]
   [demo.potion :as p]
   [recognitum.core :as rec])
  (:import
   (demo.potion Potion)))

(defn- show* [label f]
  (reset! guild/calls [])
  (println label)
  (let [out (try (str "  => " (pr-str (f)))
                 (catch clojure.lang.ExceptionInfo e
                   (str "  threw " (:error (ex-data e)) "\n  " (.replace (ex-message e) "\n" "\n  ")))
                 (catch Throwable e
                   (str "  threw " (.getName (class e)) ": " (ex-message e))))]
    (println out)
    (when (seq @guild/calls) (println "  guild calls:" (pr-str @guild/calls)))
    (println)))

(defmacro ^:private show [form] `(show* ~(pr-str form) (fn [] ~form)))

(def ^:private courage
  {::p/name "Draught of Courage"
   ::p/recipe {"dragon pepper" 2 "garlic" 1 "honey" 3}})

(defn- morning-batch
  "Fresh each call: a check remembers in place what passed on a potion."
  []
  [(p/map->Potion {::p/name "Sleeping Draught"
                   ::p/recipe {"nightshade" 1 "honey" 2}
                   ::p/label "Sleeping Draught: nightshade, honey"
                   ::p/price 30})
   (p/map->Potion {::p/name "Tonic"
                   ::p/recipe {"moonwort" 2}
                   ::p/label "Tonic: moonwort"})
   (p/map->Potion {::p/name "Mandrake Tea"
                   ::p/recipe {"mandrake root" 1 "honey" 1}
                   ::p/label "Mandrake Tea: mandrake root, honey"
                   ::p/price 8})])

(defn -main [& _]
  (println "-- each place asks for its own checks\n")
  (show (rec/checks-of p/on-the-shelf Potion))
  (show (rec/checks-of p/at-court Potion))

  (println "-- brewing checks nothing; a write takes the potion a step further\n")
  (let [brewed (p/map->Potion courage)]
    (show (rec/proves? brewed rec/shape))
    (show (rec/check brewed rec/shape))
    (show (rec/proves? brewed rec/shape))
    (show (assoc brewed ::p/colour "green"))

    (println "-- each sink gates on the context it needs: a plain map has no proof\n")
    (show (p/sell! courage))

    (println "-- on the shelf\n")
    (let [bottled (assoc brewed
                         ::p/label "Draught of Courage: dragon pepper, garlic, honey"
                         ::p/price 12)]
      (show (rec/seal bottled p/on-the-shelf))
      (show (rec/proves? bottled p/on-the-shelf))
      (show (rec/proves? bottled p/at-court))
      (show (p/sell! bottled))

      (println "-- the queen sends for it; serving and pouring each gate on the court's context\n")
      (show (p/serve-to-the-queen! bottled))
      (show (p/pour-for-the-queen! bottled))
      (show (rec/seal bottled p/at-court))
      (let [mended (assoc bottled ::p/recipe {"dragon pepper" 2 "moonwort" 1 "honey" 3})]
        (show (rec/proven-checks mended))
        (let [tasted (assoc mended ::p/taster "Sir Gulp")]
          (show (rec/seal tasted p/at-court))
          (show (rec/proves? tasted p/at-court))
          (show (p/serve-to-the-queen! tasted))
          (show (rec/proves? tasted p/on-the-shelf))
          (show (p/sell! tasted))
          (show (rec/check tasted p/on-the-shelf))

          (println "-- relabelled, it is fit for both\n")
          (let [relabelled (assoc tasted ::p/label "Draught of Courage: dragon pepper, moonwort, honey")]
            (show (rec/seal relabelled p/on-the-shelf))
            (show (rec/proves? relabelled p/at-court))
            (show (rec/proves? relabelled rec/every))
            (show (p/sell! relabelled))
            (show (p/sell! (into {} relabelled))))))))

  (println "-- the morning's batch, checked together\n")
  (show (rec/check-all (morning-batch) p/on-the-shelf)))
