(ns demo.heist-run
  "The Heist example end to end. Each printed line is a form, then what it returned or the
  error it threw; the lines that read the house also print the calls it received.

      clojure -M:dev -m demo.heist-run"
  (:require
   [clojure.edn :as edn]
   [recognitum.core :as rec]
   [demo.heist :as h]
   [demo.house :as house])
  (:import
   (demo.heist Heist)))

(defn- show* [label f]
  (reset! house/calls [])
  (println label)
  (let [out (try (str "  => " (pr-str (f)))
                 (catch clojure.lang.ExceptionInfo e
                   (str "  threw " (:error (ex-data e)) "\n  " (.replace (ex-message e) "\n" "\n  ")))
                 (catch Throwable e
                   (str "  threw " (.getName (class e)) ": " (ex-message e))))]
    (println out)
    (when (seq @house/calls) (println "  house calls:" (pr-str @house/calls)))
    (println)))

(defmacro ^:private show [form] `(show* ~(pr-str form) (fn [] ~form)))

(def ^:private crew-of-three
  {::h/name "The Italian Job"
   ::h/crew #{"Charlie" "Stella" "Lyle"}
   ::h/take 3000
   ::h/cuts {"Charlie" 1000 "Stella" 1000 "Lyle" 1000}})

(defn -main [& _]
  (println "-- building a value runs every check\n")
  (show (h/map->Heist crew-of-three))
  (show (h/map->Heist (assoc crew-of-three ::h/take 2999)))
  (show (h/->Heist "Job" #{"Charlie"} 10 {"Charlie" 10} "Handsome Rob"))
  (show (edn/read-string {:readers (rec/data-readers)}
                         "#demo.heist/Heist {:demo.heist/name \"\" :demo.heist/crew #{\"Steve\"} :demo.heist/take 0 :demo.heist/cuts {}}"))

  (println "-- a write reruns only the checks that read what it changed\n")
  (let [job h/italian-job]
    (show (assoc job ::h/getaway "Handsome Rob"))
    (show (assoc job ::h/getaway "Charlie"))
    (show (assoc job ::h/crew #{"Charlie" "Stella" "Steve"}))
    (show (merge job {::h/take 4000 ::h/cuts {"Charlie" 2000 "Stella" 1000 "Lyle" 1000}}))
    (show (assoc job :getaway-car "mini"))
    (show (instance? Heist job)))

  (println "-- a draft takes any write, remembers what passes, and seals\n")
  (let [d (into (rec/draft Heist) (assoc crew-of-three ::h/take -1))]
    (show (rec/seal d))
    (show (rec/proven-checks d))
    (show (rec/seal (assoc d ::h/take 3000)))
    (show (h/plan-from-form crew-of-three)))

  (println "-- asking a value or a draft\n")
  (show (rec/checks-of (rec/fetching house/vetted) Heist))
  (let [d (into (rec/draft Heist) crew-of-three)]
    (show (rec/check-all [h/italian-job (into (rec/draft Heist) {::h/crew #{"Steve"}}) d]
                         (rec/union rec/shape (rec/fetching house/vetted))))
    (show (rec/proven-checks d))
    (show (rec/seal d)))
  (show (rec/proves? h/italian-job rec/every))

  (println "-- asking about plain data, without building anything\n")
  (show (rec/probe Heist crew-of-three))
  (show (rec/probe Heist {::h/name "Job" ::h/crew #{"Steve"} ::h/getaway "Steve"}))
  (show (rec/probe-all Heist [crew-of-three (assoc crew-of-three ::h/crew #{"Charlie" "Stella" "Lyle" "Steve"})]))
  (show (rec/probe Heist (assoc crew-of-three ::h/crew #{"Charlie" "Stella" "Lyle" "Steve"})
                   rec/every {house/vetted (fn [names] (zipmap names (repeat true)))}))

  (println "-- a form's mistakes, all at once, as messages; the constructor stops at the first\n")
  (let [form {::h/name "Job" ::h/crew #{"Charlie" "Steve"} ::h/cuts {"Charlie" 9} ::h/gettaway "Rob"}]
    (show (h/form-errors form))
    (show (h/plan-from-form form))
    (show (h/form-errors (-> form (dissoc ::h/gettaway) (assoc ::h/take 10))))
    (show (h/form-errors crew-of-three))))
