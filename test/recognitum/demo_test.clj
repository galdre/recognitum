(ns recognitum.demo-test
  "The demos run to the end and print what each step should give, and every sink of the
  potion demo has its gate."
  (:require
   [clojure.string :as str]
   [clojure.test :refer [deftest is testing]]
   [demo.heist-run]
   [demo.potion :as p]
   [demo.potion-run]
   [recognitum.core :as rec]))

(defn- outcomes
  "The printed outcome of each step: `true`, `false` or the error it threw; any other value as
  `:value`."
  [out]
  (for [line (str/split-lines out)
        :when (re-find #"^  (=>|threw) " line)]
    (cond (= line "  => true") true
          (= line "  => false") false
          (str/starts-with? line "  threw ") (subs line (count "  threw "))
          :else :value)))

(deftest the-heist-demo-runs-to-the-end
  (is (str/includes? (with-out-str (demo.heist-run/-main)) "(rec/proves? h/italian-job rec/every)\n  => true")))

(deftest the-potion-demo-runs-to-the-end
  (let [out (with-out-str (demo.potion-run/-main))
        refused ":demo.potion/not-proven"]
    (is (= [:value :value
            false true true ":recognitum/undeclared-keys"
            refused
            :value true false :value
            refused refused ":recognitum/check-failed" :value :value true :value false refused :value
            :value true true :value refused
            :value]
           (outcomes out)))
    (is (str/includes? out "guild calls: [[:licensed [\"nightshade\" \"honey\" \"moonwort\" \"mandrake root\"]]]"))))

;;; The coverage of the potion's sinks: every public function of demo.potion whose name ends
;;; in `!` is a sink, and each refuses a potion without the proof its context asks for.

(defn- sinks []
  (for [[sym v] (ns-publics 'demo.potion)
        :when (and (str/ends-with? (name sym) "!") (fn? @v))]
    [sym @v]))

(defn- refused? [sink x]
  (= ::p/not-proven (try (sink x) nil (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))))

(deftest every-potion-sink-has-its-gate
  (is (= #{'sell! 'ring-up! 'serve-to-the-queen! 'pour-for-the-queen!} (set (map first (sinks)))))
  (let [entries {::p/name "Tonic" ::p/recipe {"moonwort" 2} ::p/label "Tonic: moonwort"
                 ::p/price 5 ::p/taster "Sir Gulp"}
        fit-for-both (rec/seal (p/map->Potion entries) rec/every)]
    (doseq [[sym sink] (sinks)]
      (testing sym
        (is (refused? sink entries) "a plain map")
        (is (refused? sink (p/map->Potion entries)) "a potion that has passed nothing")
        (is (not (refused? sink fit-for-both)) "a potion proven for both places")))))
