(ns recognitum.wide-test
  "Types with more fields than a function has parameters, against `clojure.core/defrecord`
  over the same fields.

  A Clojure function takes at most twenty parameters, so a positional constructor wider than
  that takes the rest of its arguments in one. Each operation below is asked of a type and of
  a `defrecord` twin."
  (:require
   [clojure.edn :as edn]
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]))

;;; ------------------------------------------------------------------ the types

;; One field past the limit, with no checks: every difference from the twin is one of width.
(rec/defproven Wide21 [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20])

(clojure.core/defrecord PlainWide21 [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20])

;; Five fields past the limit, with a shape check on the last: the check reads the field as a
;; local, so it pins that the arguments past the twentieth reach the fields they name.
(rec/defproven Wide25 [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24]
  rec/checks
  (f24 [] (int? f24)))

(clojure.core/defrecord PlainWide25 [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24])

;; Exactly the limit: every field is a parameter.
(rec/defproven Narrow20 [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19])

;;; ------------------------------------------------------------------ helpers

(def ^:private args25 (vec (range 25)))

(def ^:private ours21   (apply ->Wide21 (range 21)))
(def ^:private theirs21 (apply ->PlainWide21 (range 21)))
(def ^:private ours25   (apply ->Wide25 args25))
(def ^:private theirs25 (apply ->PlainWide25 args25))

(defn- bare
  "`m` with the namespace dropped from its keys, which is how the `defrecord` spells them."
  [m]
  (into {} (map (fn [[k v]] [(keyword (name k)) v])) m))

(defn- qualified
  "The first `n` fields, keyed as the types above declare them, each mapped to its index."
  [n]
  (into {} (map (fn [i] [(keyword "recognitum.wide-test" (str "f" i)) i])) (range n)))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- arity-failure
  "What the `clojure.lang.ArityException` that `f` throws reports, or nil where it throws
  none. `Plain` is dropped from the message, so the twin's message and ours are the same
  string when they say the same thing."
  [f]
  (try (f) nil
       (catch clojure.lang.ArityException e
         {:actual (.-actual e) :message (.replace (.getMessage e) "Plain" "")})))

;;; ------------------------------------------------- construction and the map surface

(deftest positional-construction-fills-every-field-as-a-defrecords-does
  (is (= (into {} theirs21) (bare ours21) (bare (qualified 21))))
  (is (= (into {} theirs25) (bare ours25) (bare (qualified 25))))
  (testing "including the fields past the twentieth, which arrive in one argument"
    (is (= 20 (:f20 theirs21) (::f20 ours21)))
    (is (= [20 21 22 23 24]
           [(:f20 theirs25) (:f21 theirs25) (:f22 theirs25) (:f23 theirs25) (:f24 theirs25)]
           [(::f20 ours25) (::f21 ours25) (::f22 ours25) (::f23 ours25) (::f24 ours25)]))))

(deftest the-positional-constructor-refuses-a-wrong-argument-count-as-a-defrecords-does
  (doseq [[width ours theirs] [[21 ->Wide21 ->PlainWide21]
                               [25 ->Wide25 ->PlainWide25]]
          given               [(dec width) (inc width)]]
    (testing (str width " fields, called with " given " arguments")
      (let [args (vec (range given))
            a    (arity-failure #(apply ours args))
            b    (arity-failure #(apply theirs args))]
        (is (= given (:actual a)) "the count reported is the count passed")
        (is (= given (:actual b)) "the defrecord reports the count passed")
        (is (= a b) "and the two describe the same mistake the same way")))))

(deftest map-construction-answers-what-a-defrecord-answers
  (is (= (into {} (map->PlainWide21 (bare (qualified 21))))
         (bare (map->Wide21 (qualified 21)))))
  (is (= (into {} (map->PlainWide25 (bare (qualified 25))))
         (bare (map->Wide25 (qualified 25)))))
  (testing "and agrees with what the positional constructor built"
    (is (= ours21 (map->Wide21 (qualified 21))))
    (is (= ours25 (map->Wide25 (qualified 25))))))

(deftest writing-a-field-past-the-twentieth-answers-what-a-defrecord-answers
  (testing "assoc"
    (is (= (into {} (assoc theirs21 :f20 :written))
           (bare (assoc ours21 ::f20 :written))))
    (is (= (into {} (assoc theirs25 :f22 :written))
           (bare (assoc ours25 ::f22 :written)))))
  (testing "merge"
    (is (= (into {} (merge theirs25 {:f21 :a :f23 :b}))
           (bare (merge ours25 {::f21 :a ::f23 :b}))))
    (is (rec/sealed? (merge ours25 {::f21 :a}))
        "a merge of declared keys is a value of the type, not a map")))

;;; ------------------------------------------------------------- what only ours does

(deftest a-wide-value-round-trips-through-the-checking-reader
  (let [back (edn/read-string {:readers (rec/data-readers)} (pr-str ours25))]
    (is (= ours25 back))
    (is (rec/sealed? back))
    (is (= 24 (::f24 back)) "the last field survives the trip")))

(deftest a-draft-of-a-wide-type-seals-into-a-value
  (let [built (rec/seal (reduce-kv assoc (rec/draft Wide25) (qualified 25)))]
    (is (= ours25 built))
    (is (rec/sealed? built))))

(deftest a-shape-check-on-a-field-past-the-twentieth-reads-that-field
  (let [e (err #(apply ->Wide25 (assoc args25 24 :not-a-number)))]
    (is (= :recognitum/check-failed (:error e)))
    (is (= [::f24] (keys (:failed e))) "the check that failed is the one on f24"))
  (testing "while a field past the twentieth that no check reads takes anything"
    (is (rec/sealed? (apply ->Wide25 (assoc args25 23 :not-a-number))))
    (is (= :not-a-number (::f23 (apply ->Wide25 (assoc args25 23 :not-a-number)))))))

;;; ------------------------------------------------------------------ the limit

(deftest a-type-of-twenty-fields-takes-them-all-as-parameters
  (is (= '([f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19])
         (:arglists (meta #'->Narrow20))))
  (let [x (apply ->Narrow20 (range 20))]
    (is (= (bare (qualified 20)) (bare x)))
    (is (rec/sealed? x)))
  (is (= 19 (:actual (arity-failure #(apply ->Narrow20 (range 19))))))
  (testing "and the arglist of a wider one names every field, past the twentieth too"
    (is (= (mapv #(symbol (str "f" %)) (range 21))
           (first (:arglists (meta #'->Wide21)))))))
