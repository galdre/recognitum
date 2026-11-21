(ns recognitum.record.types
  "The type that a value, a draft or a class belongs to, whether a definition is current, and
  how values and drafts print.

  - [[type-of]], [[type-of!]], [[type-of-class]] and [[value-type!]] find a type;
  - [[gate]] answers a type's installed write, through which the layer acts on its values;
  - [[current?]], [[named-now]] and [[current-types]] answer which definitions are current;
  - [[refuse-type!]] refuses a type given where a value belongs, and [[refuse-unnamed!]] a
    selection holding a keyword that names nothing.

  A value of any type, current or displaced, prints as its tagged literal, `#ns/T {...}`, and
  a draft as `#recognitum/draft [ns/T {...}]`. Hidden: the type each class keeps once it
  answers it, and the print-method entries."
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
  ;; each class, to a volatile that holds the type the class answers, once it answers one. A
  ;; class's answer never changes once given; nil is not kept, since a class answers nil until
  ;; its type's write is installed
  (proxy [java.lang.ClassValue] []
    (computeValue [_] (volatile! nil))))

(defn type-of-class
  "The type whose value class or draft class is `c`, as the class itself answers, or nil. Once
  given, the answer is kept on the class itself, through a `ClassValue`, so that nothing
  outside the class holds it and keeps the class loaded."
  [^Class c]
  (let [held (.get ^java.lang.ClassValue class-types c)]
    (or @held
        (when-let [t (answered-type c)]
          (vreset! held t)))))

(defn- draft-type
  "The type of a draft's memory `mo`, where that type's own installed write answers it, or
  nil: a memory built by hand around a type map that no definition made belongs to no type."
  [mo]
  (when (instance? Memo mo)
    (let [t (.-type ^Memo mo)
          g (when (map? t) (:recognitum.record/gate t))]
      (when (volatile? g)
        (when-let [g @g]
          (when (identical? t (g :recognitum.record/type nil nil)) t))))))

(defn type-of
  "The type that `x` belongs to, where `x` is a value of a type (sealed or not, current or
  displaced), a draft, a type's value class or draft class, or a type map itself. Nil for
  anything else."
  [x]
  (cond (class? x)  (type-of-class x)
        (draft? x)  (draft-type (marks-of x))
        ;; a sorted map's comparator may refuse the key, and no type is a sorted map
        (and (map? x) (not (sorted? x)) (contains? x :recognitum.record/class)) x
        (nil? x)    nil
        :else       (type-of-class (class x))))

(defn type-of!
  "[[type-of]] of `x`; throws `:recognitum/not-a-type` where `x` belongs to no type."
  [x]
  (or (type-of x)
      (throw (ex-info (str "not a value, a draft or a class of a recognitum type: " (pr-str x))
                      {:error :recognitum/not-a-type :value x}))))

(defn refuse-type!
  "Throws `:recognitum/not-a-value` where `x` is a class or is the type map `t` itself: a type
  given where a value belongs."
  [x t]
  (when (or (class? x) (identical? x t))
    (throw (ex-info (str "a type was given where a value belongs: " (:name t))
                    {:error :recognitum/not-a-value :type (:name t)}))))

(defn value-type!
  "The type of `x`, a value or a draft. Throws as [[type-of!]] and [[refuse-type!]] do for
  anything else, a type's class or type map included."
  [x]
  (let [t (type-of! x)]
    (refuse-type! x t)
    t))

(defn gate
  "The installed write of `type`, through which code without the access key makes, drafts,
  seals and checks the type's values. Called with an operation keyword and two
  arguments, it runs that operation. Read from the type map where the definition has set it
  there, else asked of the type's strategy."
  [type]
  (or (when-let [g (:recognitum.record/gate type)] (.deref ^clojure.lang.Volatile g))
      (proof/installed (:strategy type) (:recognitum.record/class type))))

(defn current?
  "Whether `type` is the current definition of its name: no later definition displaced it."
  [type]
  ((gate type) :recognitum.record/current? nil nil))

(defn named-now
  "The type whose class the namespace of type name `n` maps `n`'s name to, where that class
  belongs to a definition of `n`, current or not; else nil."
  [n]
  (let [c (some-> (find-ns (symbol (namespace n))) (.getMapping (symbol (name n))))]
    (when (class? c)
      (when-let [t (type-of-class c)]
        (when (= n (:name t)) t)))))

(defn- types-in
  "The current types whose classes namespace `n` imports under their names, each a type that
  `n` defines."
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
  "Returns selection `sel`. Throws `:recognitum/unknown-name` where a keyword in `sel` names no
  concern, no bundle check and no check of a current type of the keyword's namespace."
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
