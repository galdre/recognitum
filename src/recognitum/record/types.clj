(ns recognitum.record.types
  "The type a value, a draft or a class belongs to, and how values and drafts print.
  [[type-of]] answers the type of a value class, a sealed value, a draft or a type itself;
  [[type-of!]] refuses anything else, and [[value-type!]] a type given where a value belongs.
  [[gate]] answers a type's installed write, [[current?]] whether no later definition displaced
  a type, [[named-now]] the type a name maps to, and [[current-types]] every current type. A value
  prints as its tagged literal, and a draft as `#recognitum/draft [T {...}]`. Hidden: the answer
  each class keeps of its type, and the print-method entries."
  (:require
   [recognitum.proof :as proof]
   [recognitum.record.draft :refer [draft? marks-of]]
   [recognitum.select :as select])
  (:import
   [recognitum.record.draft Draft]
   [recognitum.record.memory Memo]))

;;; ------------------------------------------------------------------ types of values

(defn- answered-type
  "The type whose value class or draft class is `c`, as the class itself answers, or nil."
  [^Class c]
  (when-let [g (proof/gate-of c)]
    (let [t (g :recognitum.record/type nil nil)]
      (when (and (map? t) (or (identical? c (:recognitum.record/class t)) (identical? c (:recognitum.record/draft-class t))))
        t))))

(defonce ^:private class-types
  ;; each class, to a volatile holding the type its class answers once it answers one: a
  ;; class's answer never changes once given, and nil may yet become a type
  (proxy [java.lang.ClassValue] []
    (computeValue [_] (volatile! nil))))

(defn type-of-class
  "The type whose value class or draft class is `c`, as the class itself answers, or nil. The
  answer is kept on the class once given, so it leaves nothing behind that would keep the
  class loaded."
  [^Class c]
  (let [held (.get ^java.lang.ClassValue class-types c)]
    (or @held
        (when-let [t (answered-type c)]
          (vreset! held t)))))

(defn- draft-type
  "The type of a draft's memory `mo`, where that type's own gate answers it, or nil: a memory
  built by hand around a type map that no definition made names no type."
  [mo]
  (when (instance? Memo mo)
    (let [t (.-type ^Memo mo)
          g (when (map? t) (:recognitum.record/gate t))]
      (when (volatile? g)
        (when-let [g @g]
          (when (identical? t (g :recognitum.record/type nil nil)) t))))))

(defn type-of
  "The type `x` belongs to: a type's value class, a sealed value, a draft, or a type itself.
  Nil for anything else."
  [x]
  (cond (class? x)  (type-of-class x)
        (draft? x)  (draft-type (marks-of x))
        ;; a sorted map's comparator may refuse the key, and no type is a sorted map
        (and (map? x) (not (sorted? x)) (contains? x :recognitum.record/class)) x
        (nil? x)    nil
        :else       (type-of-class (class x))))

(defn type-of! [x]
  (or (type-of x)
      (throw (ex-info (str "not a value, a draft or a class of a recognitum type: " (pr-str x))
                      {:error :recognitum/not-a-type :value x}))))

(defn refuse-type!
  "Refuses `x` where `x` is `t`'s class or `t` itself, a type given where a value belongs."
  [x t]
  (when (or (class? x) (identical? x t))
    (throw (ex-info (str "a type was given where a value belongs: " (:name t))
                    {:error :recognitum/not-a-value :type (:name t)}))))

(defn value-type!
  "The type of `x`, a value or a draft; refuses anything else, a type included."
  [x]
  (let [t (type-of! x)]
    (refuse-type! x t)
    t))

(defn gate
  "The type's installed write. Each arity runs the checks it stands for. [[define-type]] keeps
  it in the type once installed; a type without it asks the strategy."
  [type]
  (or (when-let [g (:recognitum.record/gate type)] (.deref ^clojure.lang.Volatile g))
      (proof/installed (:strategy type) (:recognitum.record/class type))))

(defn current?
  "Whether `type` is the current definition of its name: no later definition displaced it."
  [type]
  ((gate type) :recognitum.record/current? nil nil))

(defn named-now
  "The type that the namespace of type name `n` maps its name to, if it is a definition of
  `n`, current or not."
  [n]
  (let [c (some-> (find-ns (symbol (namespace n))) (.getMapping (symbol (name n))))]
    (when (class? c)
      (when-let [t (type-of-class c)]
        (when (= n (:name t)) t)))))

(defn- types-in
  "The current types that namespace `n` defines: each its namespace maps its name to."
  [n]
  (for [[s c] (ns-imports n)
        :let [t (type-of-class c)]
        :when (and t (= (:name t) (symbol (str (ns-name n)) (str s))) (current? t))]
    t))

(defn current-types
  "Each type name, to the type it names now: the current definition that the name's namespace
  maps the name to."
  []
  (into {} (for [n (all-ns), t (types-in n)] [(:name t) t])))

(defn refuse-unnamed!
  "Refuses selection `sel` where a keyword in it names no concern or bundle check (see
  [[recognitum.select/named]]) and no check of a current type of the keyword's namespace.
  Returns `sel`."
  [sel]
  (doseq [k (select/keywords sel)]
    (when-not (or (select/named k)
                  (some #(contains? (:ids %) k) (some-> (namespace k) symbol find-ns types-in)))
      (throw (ex-info (str "no concern, bundle check or check of a type is named " k)
                      {:error :recognitum/unknown-name :name k}))))
  sel)

(defn- print-value
  "Prints a value of any type, current or displaced, as its tagged literal."
  [v ^java.io.Writer w]
  ;; the value printed as a map, without its meta, as `into {}` of it would print, but with no
  ;; map built
  (let [as-map (get-method print-method clojure.lang.IPersistentMap)]
    (when-let [t (type-of-class (class v))]
      (.write w (str "#" (:name t) " ")))
    (as-map (with-meta v nil) w)))

(.addMethod ^clojure.lang.MultiFn print-method recognitum.proof.Proven print-value)

(prefer-method print-method recognitum.proof.Proven clojure.lang.IPersistentMap)
(prefer-method print-method recognitum.proof.Proven java.util.Map)

(defmethod print-method Draft [^Draft d ^java.io.Writer w]
  (.write w (str "#recognitum/draft [" (:name (type-of d)) " "))
  (print-method (.-data d) w)
  (.write w "]"))
