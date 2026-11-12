(ns demo.orders
  "An ordinary domain model: an order with lines, addresses and a discount, its fields' shapes,
  its invariants, a bundle of address checks bound twice, and dry runs of an import. Each
  printed line is a form, then what it returned or the error it threw; the lines of the import
  also print the calls the catalogue received.

      clojure -M:dev -m demo.orders"
  (:require
   [clojure.string :as str]
   [recognitum.core :as rec]
   [demo.catalogue :as catalogue]
   [demo.show :refer [show *logs*]]))

(defn non-blank? [s] (and (string? s) (not (str/blank? s))))

(defn line? [x]
  (and (map? x) (non-blank? (:sku x)) (pos-int? (:qty x)) (pos-int? (:price x))))

(defn subtotal [lines] (reduce + (map #(* (:qty %) (:price %)) lines)))

(def postcode-forms
  {"US" #"\d{5}" "DE" #"\d{5}" "NL" #"\d{4} ?[A-Z]{2}" "GB" #"[A-Z]{1,2}\d[A-Z\d]? ?\d[A-Z]{2}"})

;;; ------------------------------------------------------------------ addresses, a bundle

(rec/defchecks postal-address [street postcode country]
  rec/checks
  (street-given []
    "the address has a street"
    (non-blank? street))
  (country-served []
    "the country is one the shop ships to"
    (contains? postcode-forms country))
  (postcode-fits-country [country-served]
    "the postcode has its country's form"
    (and (string? postcode) (boolean (re-matches (postcode-forms country) postcode)))))

;; A type binds a bundle once; a second address binds a copy under new names.
(rec/defcopy billing-address postal-address
  {street-given          billing-street-given
   country-served        billing-country-served
   postcode-fits-country billing-postcode-fits-country})

;;; ------------------------------------------------------------------ the order

(defprotocol Priced (total [x] "What the customer pays, in cents."))

(rec/defproven Order [id customer lines shipping ^:optional billing ^:optional discount]
  postal-address
  (street   [] (:street shipping))
  (postcode [] (:postcode shipping))
  (country  [] (:country shipping))

  ^{:when-extant billing}
  billing-address
  (street   [] (:street billing))
  (postcode [] (:postcode billing))
  (country  [] (:country billing))

  rec/checks
  (id       [] "the id is a positive whole number" (pos-int? id))
  (customer [] "the customer is named" (non-blank? customer))
  (lines    [] "the lines are a vector of sku, quantity and price" (and (vector? lines) (every? line? lines)))
  (shipping [] "the shipping address is a map" (map? shipping))
  (billing  [] "the billing address is a map" (map? billing))
  (discount [] "the discount is a whole number of cents" (nat-int? discount))

  (has-lines []
    "the order has at least one line"
    (boolean (seq lines)))
  (one-line-per-sku []
    "no sku appears on two lines"
    (= (count lines) (count (set (map :sku lines)))))
  (skus-listed []
    "the catalogue lists every sku"
    (every? true? (vals (rec/fetch-each catalogue/listed (distinct (map :sku lines))))))
  (discount-within-subtotal []
    "the discount is no more than the subtotal"
    (rec/when-extant discount (<= discount (subtotal lines))))

  Priced
  (total [_] (- (subtotal lines) (or discount 0))))

;;; ------------------------------------------------------------------ an import, tried first

(defn- problems
  "The rows that would not make an Order, from the answers of a probe of the rows: a map from
  each such row's number to the fields it lacks, the keys an Order does not have, and the
  checks that fail on it."
  [answers]
  (into (sorted-map)
        (keep-indexed
         (fn [i answer]
           ;; An answer is true, or a report of everything wrong with its row.
           (when-not (true? answer)
             [(inc i)
              ;; :missing and :undeclared are kept as they are. Of :failed, each check's
              ;; docstring is kept, less the checks that failed because they read an absent
              ;; field, which :missing already names.
              (let [failed (into (sorted-map)
                                 (for [[id {:keys [doc data]}] (:failed answer)
                                       :when (not (:absent data))]
                                   [id doc]))]
                (cond-> (select-keys answer [:missing :undeclared])
                  (seq failed) (assoc :failed failed)))])))
        answers))

(defn import-problems
  "A dry run of an import: what is wrong with each of `rows`, maps of an Order's fields as a
  sheet's parser gives them. Empty where every row would import."
  [rows]
  ;; One run over every row: the rows' reads of the catalogue go out as one call, and no
  ;; Order is built.
  (problems (rec/probe-all Order rows)))

(defn upload-problems
  "A dry run of an upload that adds the products `new-skus` and the orders `rows` in one
  transaction. The catalogue does not list the new products until the transaction commits, so
  the rows are asked against the catalogue as it will stand then."
  [new-skus rows]
  (problems
   (rec/probe-all Order rows rec/every
                  ;; For this call only, `skus-listed` reads this function in place of the
                  ;; catalogue: the catalogue's own answer, and true for each product the
                  ;; upload adds.
                  {catalogue/listed
                   (fn [skus] (merge (catalogue/listed skus)
                                     (zipmap (filter (set new-skus) skus) (repeat true))))})))

(def ^:private address {:street "1 Canal St" :postcode "1012 AB" :country "NL"})

(def ^:private two-lines
  [{:sku "tea" :qty 2 :price 450} {:sku "pot" :qty 1 :price 2900}])

(def ^:private sheet
  [{::id 11 ::customer "Ada" ::lines two-lines ::shipping address}
   {::id 12 ::customer "Grace" ::lines [{:sku "cup" :qty 4 :price 600}] ::shipping address}
   {::id 13 ::customer "Edsger" ::lines [{:sku "samovar" :qty 1 :price 9900}] ::shipping address
    ::dicsount 500}
   {::id 14 ::lines [{:sku "kettle" :qty 1 :price 3500}]
    ::shipping {:street "5 Hauptstr." :postcode "1011" :country "DE"}}])

(defn -main [& _]
  (println "-- a value runs every check, and answers its protocol\n")
  (let [o (map->Order {::id 7 ::customer "Ada" ::lines two-lines ::shipping address})]
    (show o)
    (show (total o))
    (show (rec/sealed? o))

    (println "-- a write reruns the checks that read what it changed\n")
    (show (total (assoc o ::discount 500)))
    (show (assoc o ::discount 5000))
    (show (update o ::lines conj {:sku "tea" :qty 1 :price 450}))
    (show (assoc o ::billing {:street "2 Kings Rd" :postcode "SW3 4ND" :country "GB"}))
    (show (assoc o ::billing {:street "" :postcode "12345" :country "FR"}))
    (show (assoc o ::coupon "SPRING")))

  (println "-- a failed constructor reports every failure; blocked checks did not run\n")
  (show (map->Order {::id 0 ::customer "Ada" ::lines [] ::shipping {:street "1 Main St" :postcode "9021" :country "US"}}))
  (show (map->Order {::id 8 ::customer "Ada" ::lines two-lines ::shipping "1 Main St"}))

  (println "-- an order built in steps is a draft until it seals\n")
  (let [d (-> (rec/draft Order) (assoc ::id 9 ::customer "Grace") (assoc ::lines two-lines))]
    (show (rec/check d (rec/except rec/every (rec/reading ::shipping))))
    (show (rec/seal d))
    (show (rec/seal (assoc d ::shipping {:street "5 Hauptstr." :postcode "10115" :country "DE"}))))

  (println "-- an import is tried before any row is written: every bad row is named, and the")
  (println "   catalogue is asked once for the sheet\n")
  (binding [*logs* {"catalogue" catalogue/calls}]
    (show (import-problems sheet))
    (show (import-problems (subvec sheet 0 2)))

    (println "-- the same sheet uploaded with a new product: the catalogue as it will stand\n")
    (show (upload-problems #{"samovar"} sheet)))

  (println "-- asking which checks a selection names\n")
  (show (rec/checks-of postal-address Order))
  (show (rec/checks-of (rec/reading ::discount) Order)))
