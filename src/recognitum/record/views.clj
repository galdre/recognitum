(ns recognitum.record.views
  "What a write's checks read in place of the map the write would make, and the forms of a
  type's key guards and change guard. A definition places these forms in its expansion, so
  each type's view class and guards are code of their own. `Changed` is the view of a change of
  several keys, shared by every type."
  (:require
   [recognitum.proof :as proof]))

(defn whole
  "The map `old` with `k` set to `v`, built as a map with `old`'s meta."
  [old k v]
  (with-meta (assoc (into {} (seq old)) k v) (meta old)))

(defmacro view-type
  "Defines the class named `cname` (a simple symbol, in the current namespace) of the view a
  one-key write's checks read: the map `old` with `k` set to `v`. A read of a key answers
  without building that map, and anything else builds it. A definition places this form in
  its expansion, so each type's view is a class of its own and its reads of `old` keep a
  profile per type."
  [cname]
  (let [full (symbol (str (namespace-munge *ns*) "." cname))
        [old k v x nf a b o f init args] (map #(gensym (name %)) '[old k v x nf a b o f init args])
        old (with-meta old {:tag 'clojure.lang.IPersistentMap})
        w `(whole ~old ~k ~v)]
    `(deftype* ~(symbol (str *ns*) (str cname)) ~full [~old ~k ~v]
       :implements [clojure.lang.ILookup clojure.lang.IPersistentMap clojure.lang.MapEquivalence
                    clojure.lang.IHashEq clojure.lang.IKVReduce clojure.lang.IFn java.util.Map
                    java.lang.Iterable clojure.lang.IMeta clojure.lang.IType]
       (~'valAt [this# ~x] (if (identical? ~x ~k) ~v (.valAt ~old ~x)))
       (~'valAt [this# ~x ~nf] (if (identical? ~x ~k) ~v (.valAt ~old ~x ~nf)))
       (~'containsKey [this# ~x] (or (identical? ~x ~k) (.containsKey ~old ~x)))
       (~'entryAt [this# ~x] (if (identical? ~x ~k) (clojure.lang.MapEntry/create ~k ~v) (.entryAt ~old ~x)))
       (~'assoc [this# ~a ~b] (assoc ~w ~a ~b))
       (~'assocEx [this# ~a ~b] (.assocEx ~(with-meta w {:tag 'clojure.lang.IPersistentMap}) ~a ~b))
       (~'without [this# ~a] (dissoc ~w ~a))
       (~'count [this#] (count ~w))
       (~'cons [this# ~o] (conj ~w ~o))
       (~'empty [this#] (with-meta {} (meta ~old)))
       (~'equiv [this# ~o] (= ~w ~o))
       (~'seq [this#] (seq ~w))
       (~'hasheq [this#] (hash ~w))
       (~'kvreduce [this# ~f ~init] (reduce-kv ~f ~init ~w))
       (~'invoke [this# ~x] (.valAt this# ~x))
       (~'invoke [this# ~x ~nf] (.valAt this# ~x ~nf))
       (~'applyTo [this# ~args] (clojure.lang.AFn/applyToHelper this# ~args))
       (~'size [this#] (count ~w))
       (~'isEmpty [this#] false)
       (~'get [this# ~x] (.valAt this# ~x))
       (~'containsValue [this# ~x] (.containsValue ~(with-meta w {:tag 'java.util.Map}) ~x))
       (~'keySet [this#] (.keySet ~(with-meta w {:tag 'java.util.Map})))
       (~'values [this#] (.values ~(with-meta w {:tag 'java.util.Map})))
       (~'entrySet [this#] (.entrySet ~(with-meta w {:tag 'java.util.Map})))
       (~'put [this# ~a ~b] (throw (UnsupportedOperationException.)))
       (~'remove [this# ~a] (throw (UnsupportedOperationException.)))
       (~'putAll [this# ~a] (throw (UnsupportedOperationException.)))
       (~'clear [this#] (throw (UnsupportedOperationException.)))
       (~'iterator [this#] (.iterator ~(with-meta w {:tag 'java.lang.Iterable})))
       (~'meta [this#] (meta ~old))
       (~'toString [this#] (str ~w))
       (~'hashCode [this#] (.hashCode ~(with-meta w {:tag 'java.lang.Object})))
       (~'equals [this# ~o] (.equals ~(with-meta w {:tag 'java.lang.Object}) ~o)))))

(defmacro guard-maker
  "The form of a function of `current`, a key's run `r`, the key `k`, `clean?` and `refuse`
  that answers the key's guard: it calls `(refuse old nil)` where `current` holds false, runs
  `r` on the view of `old` with `k` set to `v`, an instance of the class [[view-type]] named
  `cname` defines, and calls `(refuse old result)` where the result is not clean. Without
  `cname`, the form defines a view class of its own first. A definition places this form in
  its expansion, so each type's guards and view are code of their own and their calls keep a
  profile per type."
  ([]
   (let [cname (gensym "View")]
     `(do (view-type ~cname)
          (guard-maker ~cname))))
  ([cname]
   (let [full (symbol (str (namespace-munge *ns*) "." cname))]
     `(fn* [current# r# k# clean?# refuse#]
        (fn* [old# v#]
          (when-not (.deref ^clojure.lang.Volatile current#) (refuse# old# nil))
          (let [result# (r# (new ~full old# k# v#) nil)]
            (when-not (clean?# result#) (refuse# old# result#))))))))

(defmacro change-guard-maker
  "The form of a function of `own!`, `key-guards` (an IdentityHashMap from each declared key to
  its guard, or to `none` where its readers read a source), `removed`, `none`, `many` and
  `whole` that answers the change guard `(cg old changes)`: it calls `(own! old)`; a change
  that sets one key with a guard calls that guard, one with `none` calls `(whole old changes
  false)`, and any other calls `(many old changes)`. A definition places this form in its
  expansion, so each type's change guard is code of its own and its calls keep a profile per
  type."
  []
  (let [t (fn [tag s] (with-meta (gensym s) {:tag tag}))
        own (t 'clojure.lang.IFn "own") many (t 'clojure.lang.IFn "many") whole (t 'clojure.lang.IFn "whole")
        kg (t 'java.util.IdentityHashMap "key-guards") changes (t 'clojure.lang.IPersistentMap "changes")
        e (t 'java.util.Map$Entry "e") g (t 'clojure.lang.IFn "g")
        [removed none old v] (map gensym ["removed" "none" "old" "v"])]
    `(fn* [~own ~kg ~removed ~none ~many ~whole]
       (fn* [~old ~changes]
         (.invoke ~own ~old)
         (if (== 1 (.count ~changes))
           (let [~e (.next (.iterator ~(with-meta changes {:tag 'java.lang.Iterable})))
                 ~v (.getValue ~e)
                 ~g (when-not (identical? ~v ~removed) (.get ~kg (.getKey ~e)))]
             (cond (nil? ~g) (.invoke ~many ~old ~changes)
                   (identical? ~g ~none) (.invoke ~whole ~old ~changes false)
                   :else (.invoke ~g ~old ~v)))
           (.invoke ~many ~old ~changes))))))

;;; ------------------------------------------------------------------ changes

(def ^:private none (Object.))

(defn- applied
  "The map `old` with `changes` applied, built as a map with `old`'s meta: each key of
  `changes` set to its value, or removed where its value is `removed`."
  [old changes removed]
  (reduce-kv (fn [m k v] (if (identical? v removed) (dissoc m k) (assoc m k v)))
             (proof/plain-map old) changes))

(deftype ^:private Changed [^clojure.lang.IPersistentMap old ^clojure.lang.IPersistentMap changes removed]
  ;; The view a change's checks read: the map `old` with `changes` applied, as [[applied]]
  ;; builds it. A read of a key answers without building that map, and anything else builds it.
  clojure.lang.ILookup
  (valAt [this x] (.valAt this x nil))
  (valAt [_ x nf] (let [v (.valAt changes x none)]
                    (cond (identical? v none)    (.valAt old x nf)
                          (identical? v removed) nf
                          :else                  v)))
  clojure.lang.IPersistentMap
  (containsKey [_ x] (let [v (.valAt changes x none)]
                       (if (identical? v none) (.containsKey old x) (not (identical? v removed)))))
  (entryAt [this x] (when (.containsKey this x) (clojure.lang.MapEntry/create x (.valAt this x))))
  (assoc [_ a b] (assoc (applied old changes removed) a b))
  (assocEx [_ a b] (.assocEx ^clojure.lang.IPersistentMap (applied old changes removed) a b))
  (without [_ a] (dissoc (applied old changes removed) a))
  (count [_] (count (applied old changes removed)))
  (cons [_ o] (conj (applied old changes removed) o))
  (empty [_] (with-meta {} (meta old)))
  (equiv [_ o] (= (applied old changes removed) o))
  (seq [_] (seq (applied old changes removed)))
  (iterator [_] (.iterator ^Iterable (applied old changes removed)))
  clojure.lang.MapEquivalence
  clojure.lang.IHashEq
  (hasheq [_] (hash (applied old changes removed)))
  clojure.lang.IKVReduce
  (kvreduce [_ f init] (reduce-kv f init (applied old changes removed)))
  clojure.lang.IFn
  (invoke [this x] (.valAt this x))
  (invoke [this x nf] (.valAt this x nf))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))
  java.util.Map
  (size [_] (count (applied old changes removed)))
  (isEmpty [_] (zero? (count (applied old changes removed))))
  (get [this x] (.valAt this x))
  (containsValue [_ x] (.containsValue ^java.util.Map (applied old changes removed) x))
  (keySet [_] (.keySet ^java.util.Map (applied old changes removed)))
  (values [_] (.values ^java.util.Map (applied old changes removed)))
  (entrySet [_] (.entrySet ^java.util.Map (applied old changes removed)))
  (put [_ _ _] (throw (UnsupportedOperationException.)))
  (remove [_ _] (throw (UnsupportedOperationException.)))
  (putAll [_ _] (throw (UnsupportedOperationException.)))
  (clear [_] (throw (UnsupportedOperationException.)))
  clojure.lang.IMeta
  (meta [_] (meta old))
  Object
  (toString [_] (str (applied old changes removed)))
  (hashCode [_] (.hashCode ^Object (applied old changes removed)))
  (equals [_ o] (.equals ^Object (applied old changes removed) o)))
