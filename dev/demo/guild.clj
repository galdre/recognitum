(ns demo.guild
  "A stand-in for the apothecaries' guild register: which herbs a member may sell. It is in
  memory and logs every call, so a caller can see what a check read and how often.")

(def ^:private register
  {"dragon pepper" true "garlic" true "honey" true "moonwort" true "mandrake root" true
   "nightshade" false})

(defonce calls (atom []))

(defn licensed
  "A source: for each herb, whether the guild licenses it for sale. An herb it has never heard
  of is not licensed."
  [herbs]
  (swap! calls conj [:licensed herbs])
  (into {} (map (fn [h] [h (get register h false)])) herbs))
