(ns demo.catalogue
  "A stand-in for the shop's catalogue: which skus it sells. It is in memory and logs every
  call, so a caller can see what a check read and how often.")

(def ^:private skus #{"tea" "pot" "cup" "kettle"})

(defonce calls (atom []))

(defn listed
  "A source: for each sku, whether the catalogue lists it."
  [ks]
  (swap! calls conj [:listed ks])
  (into {} (map (fn [k] [k (contains? skus k)])) ks))
