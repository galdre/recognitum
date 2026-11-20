(ns recognitum.redefinition-test
  "Redefinition beyond the namespace's mapping: what a definition keeps alive, two definitions
  of one name at once, and a definition evaluated in a removed namespace object that something
  still holds."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- scratch-ns
  "A new namespace with `clojure.core` referred, named from `prefix` and the clock."
  [prefix]
  (let [n (create-ns (symbol (str "recognitum.redefinition-test." prefix (System/nanoTime))))]
    (binding [*ns* n] (refer-clojure))
    n))

(defn- define-in
  "Evaluates `(rec/defproven X [a] ...)` with `*ns*` bound to `n`, the check on `a` being
  `body`. Returns what the definition returns, the value class."
  [n body]
  (binding [*ns* n]
    (eval (list 'recognitum.core/defproven 'X '[a] 'recognitum.core/checks (list 'a [] body)))))

(defn- a-of [n] (keyword (str (ns-name n)) "a"))

;;; ---- what a definition keeps alive

(def ^:private class-cache
  "Clojure's cache of the classes its loaders define, by name, each held softly."
  (delay (let [f (doto (.getDeclaredField clojure.lang.DynamicClassLoader "classCache")
                   (.setAccessible true))]
           (.get f nil))))

(defn- collected?
  "Whether `r`'s referent is cleared within 50 requests for a collection."
  [^java.lang.ref.WeakReference r]
  (loop [i 0]
    (cond (nil? (.get r)) true
          (= i 50) false
          :else (do (System/gc) (Thread/sleep 20) (recur (inc i))))))

(deftest a-definition-nothing-holds-is-collected-with-its-class
  "Defines a type under a fresh name, makes a value, removes the namespace, and drops every
  reference; then removes the entries the definition added to Clojure's class cache, which
  holds them softly until memory runs short, and asks for collections until a weak reference
  to the type's class clears. So the library, the table of the definitions a later one
  displaces among it, holds the definition only weakly. It does not prove that a JVM collects
  without memory pressure, since that cache keeps the classes until then, nor anything about a
  type with protocols, whose caches are Clojure's."
  (let [^java.util.Map cache @class-cache
        before (set (keys cache))
        r (let [n (scratch-ns "gone")
                cls (define-in n '(int? a))
                v (@(ns-resolve n 'map->X) {(a-of n) 1})]
            (is (rec/sealed? v))
            (remove-ns (ns-name n))
            (java.lang.ref.WeakReference. cls))]
    (doseq [k (keys cache) :when (not (contains? before k))]
      (.remove cache k))
    (is (collected? r))))

;;; ---- two definitions at once

(deftest two-threads-defining-one-name-leave-exactly-one-current-definition
  "Two threads define one name twenty times each, at once. Each definition displaces the one
  current before it, so afterwards exactly one of the forty classes seals a draft, and a value
  of the definition current before them is not sealed. A guard, not a proof: an interleaving
  that would lose or keep a definition may not occur in a run."
  (let [n (scratch-ns "race")
        _ (define-in n '(int? a))
        a (a-of n)
        v0 (@(ns-resolve n 'map->X) {a 1})
        start (java.util.concurrent.CountDownLatch. 1)
        run (fn [] (.await start) (vec (repeatedly 20 #(define-in n '(int? a)))))
        fs [(future (run)) (future (run))]
        _ (.countDown start)
        classes (into [] (mapcat deref) fs)
        seals? (fn [cls] (nil? (err #(rec/seal (into (rec/draft cls) {a 1})))))]
    (try
      (is (= 40 (count (set classes))))
      (is (= 1 (count (filter seals? classes))))
      (is (false? (rec/sealed? v0)))
      (finally (remove-ns (ns-name n))))))

;;; ---- a removed namespace object that something still holds

(deftest a-definition-in-a-held-removed-namespace-object-displaces-by-name
  "Define X in n (D1); remove n, holding its object; load n again and define X (D2); define X
  with `*ns*` bound to the held object (D3). D3 displaces D2 by name, and D1 stays displaced:
  values of both are not sealed. The held object's `map->X` is D1's constructor, held from
  before the redefinition, and refuses."
  (let [held (scratch-ns "held")
        nsym (ns-name held)
        a (a-of held)]
    (try
      (define-in held '(int? a))
      (let [held-make @(ns-resolve held 'map->X)
            v1 (held-make {a 1})
            _ (remove-ns nsym)
            live (create-ns nsym)
            _ (binding [*ns* live] (refer-clojure))
            _ (define-in live '(int? a))
            v2 (@(ns-resolve live 'map->X) {a 1})
            sealed-before [(rec/sealed? v1) (rec/sealed? v2)]
            _ (define-in held '(int? a))]
        (is (= [false true] sealed-before))
        (is (false? (rec/sealed? v1)))
        (is (false? (rec/sealed? v2)))
        (is (= :recognitum/displaced-constructor (:error (err #(@(.findInternedVar ^clojure.lang.Namespace held 'map->X) {a 1}))))))
      (finally (remove-ns nsym)))))
