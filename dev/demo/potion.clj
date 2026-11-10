(ns demo.potion
  "The second worked example: a potion brewed step by step, and the two places it may go. The
  shop sells a potion that is labelled, priced and made of licensed herbs; the queen drinks one
  that a taster has drunk first and that holds nothing she cannot abide. One potion can be fit
  for either place, for both, or for neither, and a context names each place's checks."
  (:require
   [clojure.string :as str]
   [demo.guild :as guild]
   [recognitum.core :as rec]))

(defn non-blank? [s] (and (string? s) (not (str/blank? s))))
(defn recipe? [x] (and (map? x) (seq x) (every? non-blank? (keys x)) (every? pos-int? (vals x))))

(def the-queen-cannot-abide #{"garlic" "mandrake root"})

(rec/defconcern shop "What the shop needs before it sells a potion.")
(rec/defconcern court "What the court needs before the queen drinks a potion.")

(rec/defproven-in Potion [name recipe ^:optional label ^:optional price ^:optional taster]
  rec/checks
  (name   [] "the potion has a name" (non-blank? name))
  (recipe [] "the recipe maps each herb to its drams" (recipe? recipe))
  (label  [] "the label is written" (non-blank? label))
  (price  [] "the price is a whole number of pennies" (pos-int? price))
  (taster [] "the taster is named" (non-blank? taster))

  (labelled [] ::shop
    "the label names every herb"
    (every? #(str/includes? label %) (keys recipe)))
  (priced [] ::shop
    "the potion has a price"
    (rec/extant? price))
  (licensed [] ::shop
    "the guild licenses every herb"
    (every? true? (vals (rec/fetch-each guild/licensed (keys recipe)))))

  (tasted [] ::court
    "a taster drank it first"
    (rec/extant? taster))
  (fit-for-the-queen [] ::court
    "it holds nothing the queen cannot abide"
    (not-any? the-queen-cannot-abide (keys recipe))))

(rec/defcontext on-the-shelf
  "Sold in the shop: every check but the court's."
  (rec/except rec/every court))

(rec/defcontext at-court
  "Served to the queen: every check but the shop's."
  (rec/except rec/every shop))

;;; The sinks: the functions whose effect depends on a potion's checks having passed. Each
;;; names the context it needs and gates on it, so a potion proven for one place is refused
;;; in the other, and a plain map is refused everywhere. Coverage, the assurance that every
;;; sink has its gate, comes from a test: demo-test hands every function here whose name ends
;;; in `!` a potion without proof and expects a refusal.

(defn- gate
  "Throws unless `potion` is proven against the context held by the var `context`."
  [potion context sink]
  (when-not (rec/proves? potion @context)
    (throw (ex-info (str sink " takes only a potion proven " (:name (meta context)))
                    {:error ::not-proven :sink sink :context (symbol context)}))))

(defonce till (atom []))
(defonce royal-cup (atom nil))

(defn ring-up!
  "Records the sale of `potion` in the shop's till, and returns the receipt. Refuses a potion
  not proven `on-the-shelf`."
  [potion]
  (gate potion #'on-the-shelf 'ring-up!)
  (let [receipt {:sold (::name potion) :pennies (::price potion)}]
    (swap! till conj receipt)
    receipt))

(defn sell!
  "Sells `potion` over the counter. Refuses a potion not proven `on-the-shelf`."
  [potion]
  (gate potion #'on-the-shelf 'sell!)
  (ring-up! potion))

(defn pour-for-the-queen!
  "Fills the queen's cup with `potion`, and returns what the cup holds. Refuses a potion not
  proven `at-court`."
  [potion]
  (gate potion #'at-court 'pour-for-the-queen!)
  (reset! royal-cup (::name potion)))

(defn serve-to-the-queen!
  "Serves `potion` to the queen. Refuses a potion not proven `at-court`."
  [potion]
  (gate potion #'at-court 'serve-to-the-queen!)
  (pour-for-the-queen! potion))
