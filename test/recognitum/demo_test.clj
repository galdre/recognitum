(ns recognitum.demo-test
  "The demos run to the end and print what each step should give, their functions answer what
  the documentation says of them, and every sink of the demos has its gate."
  (:require
   [clojure.string :as str]
   [clojure.test :refer [deftest is testing]]
   [demo.authz :as authz]
   [demo.guild :as guild]
   [demo.heist :as heist]
   [demo.heist-run]
   [demo.orders :as orders]
   [demo.permissions :as perms]
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
  (let [out (with-out-str (demo.heist-run/-main))]
    (is (str/includes? out "(rec/proves? h/italian-job rec/every)\n  => true"))
    (is (str/includes? out "(rec/probe Heist crew-of-three)\n  => true"))
    (is (re-find #":missing #\{:demo.heist/(cuts|take) :demo.heist/(cuts|take)\}" out))))

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

;;; The coverage of the sinks. Every public function of demo.potion whose name ends in `!` is
;;; a sink, and each takes only a potion with the proof its context asks for. The refund demo
;;; has one sink, `issue!`, which takes only a sealed Refund.

(defn- sinks []
  (for [[sym v] (ns-publics 'demo.potion)
        :when (and (str/ends-with? (name sym) "!") (fn? @v))]
    [sym @v]))

(defn- refusal
  "The exception `sink` throws when handed `x`, or nil where it accepts `x`."
  [sink x]
  (try (sink x) nil (catch clojure.lang.ExceptionInfo e e)))

(defn- refused? [sink x]
  (= ::p/not-proven (:error (ex-data (refusal sink x)))))

(defn- displaced-jar
  "A value of a type that was redefined after the value was made."
  []
  (let [n (create-ns 'recognitum.demo-test.cellar)
        define '(recognitum.core/defproven Jar [size] recognitum.core/checks (size [] (int? size)))]
    (try (binding [*ns* n]
           (refer-clojure)
           (eval define)
           (let [jar ((ns-resolve n 'map->Jar) {:recognitum.demo-test.cellar/size 1})]
             (eval define)
             jar))
         (finally (remove-ns (ns-name n))))))

(def ^:private not-potions
  "What no potion sink may take, by name: values that are not potions, with and without proof."
  {"a plain map" {}
   "nil" nil
   "a sealed value of another type" heist/italian-job
   "a draft of another type" (into (rec/draft demo.heist.Heist) heist/italian-job)
   "a value of a redefined type" (displaced-jar)})

(deftest every-potion-sink-has-its-gate
  (is (= #{'sell! 'ring-up! 'serve-to-the-queen! 'pour-for-the-queen!} (set (map first (sinks)))))
  (is (rec/sealed? heist/italian-job))
  (let [entries {::p/name "Tonic" ::p/recipe {"moonwort" 2} ::p/label "Tonic: moonwort"
                 ::p/price 5 ::p/taster "Sir Gulp"}
        fit-for-both (rec/seal (p/map->Potion entries) rec/every)]
    (doseq [[sym sink] (sinks)]
      (testing sym
        (is (refused? sink entries) "a plain map with a potion's entries")
        (is (refused? sink (p/map->Potion entries)) "a potion that has passed nothing")
        (is (not (refused? sink fit-for-both)) "a potion proven for both places")
        (doseq [[what x] not-potions]
          (is (refused? sink x) what))
        (testing "the refusal names the class of what it was handed"
          (is (str/includes? (str (ex-message (refusal sink heist/italian-job))) "demo.heist.Heist")))))))

(deftest a-refused-potion-reaches-neither-the-till-nor-the-cup
  (let [till @p/till
        cup @p/royal-cup]
    (doseq [[_ sink] (sinks)
            x (vals not-potions)]
      (refusal sink x))
    (is (= till @p/till))
    (is (= cup @p/royal-cup))))

(deftest the-refund-sink-has-its-gate
  (perms/restore!)
  (let [draft (authz/request->draft {:session {:user "dana"} :params {"order" "42" "amount" "1500"}})
        refused? #(= "not a sealed Refund" (ex-message (refusal authz/issue! %)))]
    (is (not (refused? (rec/seal draft))) "a sealed Refund")
    (is (refused? draft) "a Refund's draft")
    (is (refused? (into {} draft)) "a plain map with a refund's entries")
    (doseq [[what x] not-potions]
      (is (refused? x) what))))

;;; What the demos' functions answer.

(deftest the-heist-s-form-errors-name-every-mistake-at-once
  (is (= ["take is required"
          "gettaway is not a field of a heist"
          "check failed: the house has vetted everyone on the crew"]
         (heist/form-errors {::heist/name "Job" ::heist/crew #{"Charlie" "Steve"}
                             ::heist/cuts {"Charlie" 9} ::heist/gettaway "Rob"}))))

(def ^:private address {:street "1 Canal St" :postcode "1012 AB" :country "NL"})

(deftest a-dry-run-of-an-import-names-every-bad-row
  (is (= {2 {:undeclared #{::orders/dicsount}
             :failed {::orders/skus-listed "the catalogue lists every sku"}}
          3 {:missing #{::orders/customer}
             :failed {::orders/postcode-fits-country "the postcode has its country's form"}}}
         (orders/import-problems
          [{::orders/id 11 ::orders/customer "Ada" ::orders/lines [{:sku "tea" :qty 2 :price 450}]
            ::orders/shipping address}
           {::orders/id 13 ::orders/customer "Edsger"
            ::orders/lines [{:sku "samovar" :qty 1 :price 9900}] ::orders/shipping address
            ::orders/dicsount 500}
           {::orders/id 14 ::orders/lines [{:sku "kettle" :qty 1 :price 3500}]
            ::orders/shipping {:street "5 Hauptstr." :postcode "1011" :country "DE"}}]))))

(deftest a-dry-run-of-an-upload-counts-its-new-products-as-listed
  (is (= {2 {:failed {::orders/skus-listed "the catalogue lists every sku"}}}
         (orders/upload-problems
          #{"samovar"}
          [{::orders/id 13 ::orders/customer "Edsger"
            ::orders/lines [{:sku "samovar" :qty 1 :price 9900}] ::orders/shipping address}
           {::orders/id 15 ::orders/customer "Ada"
            ::orders/lines [{:sku "urn" :qty 1 :price 7000}] ::orders/shipping address}]))))

(deftest refunds-are-asked-under-another-limit-and-under-an-earlier-day-s-grants
  (perms/restore!)
  (try
    (let [waiting [{::authz/actor "eli" ::authz/order-id 42 ::authz/amount 2500}
                   {::authz/actor "eli" ::authz/order-id 42 ::authz/amount 900}]]
      (is (= [false true] (mapv true? (rec/probe-all demo.authz.Refund waiting))))
      (is (= [true true] (mapv true? (authz/under-limit waiting "eli" 3000))))
      (is (= [false false] (mapv true? (authz/under-limit waiting "eli" 500))))
      (is (= [false true] (mapv true? (rec/probe-all demo.authz.Refund waiting)))
          "the service's limit is unchanged"))
    (perms/revoke! "dana" :refund 42)
    (let [issued [{::authz/actor "dana" ::authz/order-id 42 ::authz/amount 1500}
                  {::authz/actor "eli" ::authz/order-id 41 ::authz/amount 300}]
          that-day {:grants #{["dana" :refund 42]} :limits {"dana" 5000 "eli" 1000}}]
      (is (= [false false] (mapv true? (rec/probe-all demo.authz.Refund issued))))
      (is (= [true false] (mapv true? (authz/valid-on-the-day issued that-day)))))
    (finally (perms/restore!))))

(defn- failed-checks
  "The ids of the checks that fail when `f` is called, or nil where `f` returns."
  [f]
  (try (f) nil
       (catch clojure.lang.ExceptionInfo e (set (keys (:failed (ex-data e)))))))

(deftest a-potion-is-proven-for-one-place-at-a-time
  (reset! guild/calls [])
  (let [brewed (p/map->Potion {::p/name "Draught of Courage"
                               ::p/recipe {"dragon pepper" 2 "garlic" 1 "honey" 3}})]
    (testing "a brewed potion has passed nothing, and a check records what passed"
      (is (false? (rec/proves? brewed rec/shape)))
      (is (true? (rec/check brewed rec/shape)))
      (is (true? (rec/proves? brewed rec/shape))))
    (let [bottled (assoc brewed
                         ::p/label "Draught of Courage: dragon pepper, garlic, honey"
                         ::p/price 12)]
      (is (true? (rec/check bottled p/shop)))
      (is (true? (rec/proves? bottled p/shop)))
      (is (false? (rec/proves? bottled p/court)))
      (let [mended (assoc bottled ::p/recipe {"dragon pepper" 2 "moonwort" 1 "honey" 3})]
        (testing "a write forgets each check that reads a key it changes"
          (is (false? (rec/proves? mended p/shop)))
          (is (= #{::p/name ::p/label ::p/price ::p/taster ::p/priced} (rec/proven-checks mended)))
          (is (true? (rec/proves? bottled p/shop))))
        (testing "a seal against one context"
          (is (identical? bottled (rec/seal bottled p/on-the-shelf)))
          (is (= #{::p/fit-for-the-queen ::p/tasted} (failed-checks #(rec/seal bottled p/at-court))))
          (is (= (str "demo.potion/Potion failed 2 checks\n"
                      "  :demo.potion/fit-for-the-queen (it holds nothing the queen cannot abide): false\n"
                      "  :demo.potion/tasted (a taster drank it first): false")
                 (ex-message (refusal #(rec/seal % p/at-court) bottled)))))
        (let [served (assoc mended ::p/taster "Sir Gulp")]
          (is (identical? served (rec/seal served p/at-court)))
          (is (false? (rec/proves? served p/on-the-shelf)))
          (is (= {:failed {::p/labelled {:data false :blocked #{} :doc "the label names every herb"}}
                  :blocked #{}}
                 (rec/check served p/on-the-shelf)))
          (let [relabelled (assoc served ::p/label "Draught of Courage: dragon pepper, moonwort, honey")
                message    #(ex-message (refusal %1 %2))]
            (testing "the label's write forgot only the checks that read the label"
              (is (= #{::p/label ::p/labelled}
                     (apply disj (rec/checks-of rec/every demo.potion.Potion)
                            (rec/proven-checks relabelled))))
              (is (identical? relabelled (rec/seal relabelled p/on-the-shelf)))
              (is (true? (rec/proves? relabelled p/at-court))))
            (testing "each sink says what it takes and what it was handed"
              (is (= (str "sell! takes only a potion proven on-the-shelf, not a value of class "
                          "clojure.lang.PersistentArrayMap")
                     (message p/sell! {::p/name "Draught of Courage"
                                       ::p/recipe {"dragon pepper" 2 "garlic" 1 "honey" 3}})
                     (message p/sell! (into {} relabelled))))
              (is (= {:sold "Draught of Courage" :pennies 12} (p/sell! relabelled)))
              (is (= (str "serve-to-the-queen! takes only a potion proven at-court, "
                          "not a potion without that proof")
                     (message p/serve-to-the-queen! bottled)))
              (is (= (str "pour-for-the-queen! takes only a potion proven at-court, "
                          "not a potion without that proof")
                     (message p/pour-for-the-queen! bottled)))
              (is (= "Draught of Courage" (p/serve-to-the-queen! served)))))))))
  (is (seq @guild/calls) "the shop's checks read the guild"))
