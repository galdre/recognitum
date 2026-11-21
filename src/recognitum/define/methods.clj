(ns recognitum.define.methods
  "The sections of methods of a definition:

  - what a section's head names: [[protocol-var]], [[interface-named]], [[class-named]], or why
    it heads no section, [[head-refusal]];
  - the methods of a protocol's section, [[parse-protocol]], and of an interface's,
    [[parse-interface]];
  - the function that each method compiles to: [[method-fn]];
  - the refusals of a section or a method written twice, [[check-method-sections!]] and
    [[check-methods!]], and of a definition that the proof strategy refuses,
    [[refuse-definition!]].

  Each function returns data or a form, or throws the refusal of the definition. Hidden: the
  type hints and primitives of an interface's methods, and how a protocol's methods are read."
  (:require
   [clojure.string :as str]
   [recognitum.body :refer [fail!]]
   [recognitum.define.clauses :refer [resolve-var words]]))

(defn protocol-var
  "The var that `s` resolves to, where that var holds a protocol; else nil."
  [s]
  (when-let [v (resolve-var s)] (let [x @v] (when (and (map? x) (:on-interface x)) v))))

(defn class-named [s] (try (let [c (resolve s)] (when (class? c) c)) (catch Exception _ nil)))

(defn interface-named
  "The class `s` names, where it may head a section of methods: an interface, or `Object`."
  [s]
  (when-let [^Class c (class-named s)] (when (or (= Object c) (.isInterface c)) c)))

(defn head-refusal
  "Why `s` heads no section: it names a class that is not an interface, a var that is neither a
  bundle nor a protocol, or nothing."
  [s]
  (cond (class-named s) (str s " is a class, not a protocol or an interface: of the classes, a defproven type"
                             " implements interfaces and Object's toString")
        (resolve-var s) (str s " is not a bundle, a protocol or an interface")
        :else (str s " names no bundle var, no protocol and no interface")))

(defn- parse-method
  "One method of the section headed by `marker`: `(name [this params...] body...)`, refused where
  `defrecord` refuses it: no first parameter, or parameters other than plain symbols."
  [ctx marker m]
  (let [ctx (assoc ctx :line (:line (meta m)))
        [nm params & body] m]
    (when-not (and (seq? m) (simple-symbol? nm) (vector? params))
      (fail! ctx (str "a method of " marker " is (name [this params...] body...): " (pr-str m))))
    (when (empty? params)
      (fail! ctx (str "method " nm " of " marker " needs a first parameter, for the value")))
    (when-not (and (every? simple-symbol? params) (not-any? #{'&} params))
      (fail! ctx (str "the parameters of method " nm " of " marker " are plain symbols: " (pr-str params))))
    {:name nm :params params :body body :line (:line (meta m)) :marker marker}))

(defn- parameters [n] (if (= 1 n) " parameter" " parameters"))

(defn parse-protocol
  "A protocol section's methods, each with the signature of its interface's method, refused
  where `defrecord` refuses them: a method the protocol does not declare, and an arity it does
  not declare."
  [ctx {:keys [protocol marker methods]}]
  (let [sigs (:sigs @protocol)]
    (for [m methods
          :let [{:keys [name params line] :as impl} (parse-method ctx marker m)
                ctx (assoc ctx :line line)
                sig (get sigs (keyword (clojure.core/name name)))
                arities (set (map count (:arglists sig)))]]
      (do (when-not sig
            (fail! ctx (str marker " has no method " name ". Its methods: "
                            (words (sort (map clojure.core/name (keys sigs)))))))
          (when-not (arities (count params))
            (fail! ctx (str "method " name " of " marker " takes " (str/join " or " (sort arities))
                            (parameters (apply max arities)) ", the value first, not " (count params))))
          (assoc impl
                 :protocol? true
                 :sig [(munge (clojure.core/name name)) (vec (repeat (dec (count params)) Object))])))))

(def ^:private primitives
  {'long Long/TYPE 'int Integer/TYPE 'double Double/TYPE 'float Float/TYPE 'boolean Boolean/TYPE
   'char Character/TYPE 'byte Byte/TYPE 'short Short/TYPE})

(defn- hint-class
  "The class that the type hint on parameter `p` names, or nil where it has none."
  [ctx nm p]
  (when-let [tag (:tag (meta p))]
    (or (primitives tag)
        (when (symbol? tag) (class-named tag))
        (when (string? tag) (try (Class/forName tag) (catch ClassNotFoundException _ nil)))
        (fail! ctx (str "the hint ^" tag " on parameter " p " of method " nm " names no class")))))

(defn- show-method [^java.lang.reflect.Method m]
  (str (.getName m) "(" (str/join ", " (map #(.getName ^Class %) (.getParameterTypes m))) ")"))

(defn parse-interface
  "An interface section's methods, each with the signature of the one method of the interface
  that it implements. Of the methods of `Object`, a section headed by `Object` may give only
  `toString`. Refuses:

  - a method that the interface does not declare, and an arity that it does not declare;
  - `equals` and `hashCode`, since a value's equality and hash are its map's;
  - a hint on a parameter that names no class;
  - a method that, after the hints on its parameters, matches none of the interface's methods,
    or more than one."
  [ctx {:keys [^Class class marker methods]}]
  (for [m methods
        :let [{:keys [name params line] :as impl} (parse-method ctx marker m)
              ctx (assoc ctx :line line)
              n (munge (clojure.core/name name))
              args (rest params)
              _ (when (#{"equals" "hashCode"} n)
                  (fail! ctx (str "method " n " of " marker ": a value's equality and hash are its map's,"
                                  " so a type gives neither equals nor hashCode")))
              declared (if (= Object class)
                         (if (= "toString" n)
                           [(.getMethod Object "toString" (make-array Class 0))]
                           (fail! ctx (str "method " n " of Object: of Object's methods, a type gives only toString")))
                         (filter #(and (= n (.getName ^java.lang.reflect.Method %))
                                       (not (java.lang.reflect.Modifier/isStatic (.getModifiers ^java.lang.reflect.Method %))))
                                 (.getMethods class)))
              _ (when (empty? declared)
                  (fail! ctx (str marker " declares no method " n ". Its methods: "
                                  (words (sort (distinct (map #(.getName ^java.lang.reflect.Method %)
                                                              (.getMethods class))))))))
              of-arity (filter #(= (count args) (.getParameterCount ^java.lang.reflect.Method %)) declared)
              _ (when (empty? of-arity)
                  (let [arities (sort (distinct (map #(inc (.getParameterCount ^java.lang.reflect.Method %)) declared)))]
                    (fail! ctx (str "method " n " of " marker " takes " (str/join " or " arities)
                                    (parameters (last arities)) ", the value first, not " (count params)))))
              hints (mapv #(hint-class ctx n %) args)
              found (filter (fn [^java.lang.reflect.Method jm]
                              (every? true? (map (fn [h c] (or (nil? h) (= h c))) hints (.getParameterTypes jm))))
                            of-arity)]]
    (case (count found)
      0 (fail! ctx (str "no method " n " of " marker " takes the hinted types: "
                        (words (map show-method of-arity))))
      1 (assoc impl :sig [n (vec (.getParameterTypes ^java.lang.reflect.Method (first found)))])
      (fail! ctx (str "method " n " of " marker ": " (count found) " methods take " (count args)
                      (parameters (count args)) " after the value; hint the parameters' types to choose one: "
                      (words (map show-method found)))))))

(defn refuse-definition!
  "Throws the proof strategy's refusal of the definition of `tname`, a map
  `{:kind :message :method}`, located at the method of `methods` that `:method` names. Where
  `:kind` is `:map-method`, the method is one that a value already has as a map, and the message
  gives the remedies: a protocol's method is renamed, or extended to the type after the
  definition; an interface's method is left out, since the map's method answers it. Otherwise
  the message is the strategy's `:message`."
  [ctx tname methods {:keys [kind message method]}]
  (let [[mname arity] method
        impl (when method
               (some #(when (= [mname arity] [(symbol (first (:sig %))) (count (second (:sig %)))]) %) methods))
        ctx (cond-> ctx impl (assoc :line (:line impl)))]
    (fail! ctx (if (and (= :map-method kind) impl)
                 (let [{:keys [name marker protocol?]} impl]
                   (str "method " name " of " marker ": as a map, a value of " tname " already has a method " name
                        " of " arity (parameters arity) ", so the type cannot give it: "
                        (if protocol?
                          (str "rename it, or extend " marker " to " tname " with extend-protocol after the"
                               " definition (a method extended from outside is not guarded: it answers on"
                               " values of a displaced definition)")
                          "leave it out, and the map's method answers")))
                 message))))

(defn- hints-own-class
  "A form in `forms` whose type hint names the type `tname` or its class `classname`, or nil."
  [tname classname forms]
  (first (for [f (tree-seq coll? seq forms)
               :let [tag (:tag (meta f))]
               :when (and tag (#{tname (symbol classname)} (if (string? tag) (symbol tag) tag)))]
           f)))

(defn method-fn
  "The form of a fn of `current` and `refuse`, as `recognitum.record/define-type` takes a
  method. That fn returns the fn that implements the method, which is called with the value
  first:

  - where `@current` is false or nil, it returns what `refuse` returns given the value;
  - else it runs the body with each field bound to its entry in the value (nil where absent),
    the first parameter bound to the value, and the type's name bound to the value's class.

  `recur` in the body goes to the method's head with the parameters after the first, as in
  `defrecord`."
  [tname fields key-of {:keys [params body]}]
  (let [[self & args] params
        v (gensym "value")
        current (gensym "current")
        refuse (gensym "refuse")
        gs (mapv #(gensym (str (name %) "_")) args)
        args (map #(cond-> % (primitives (:tag (meta %))) (vary-meta dissoc :tag)) args)]
    `(fn [~current ~refuse]
       (fn [~v ~@gs]
         (if (.deref ~(with-meta current {:tag 'clojure.lang.IDeref}))
           (let [~tname (class ~v)
                 ~@(mapcat (fn [f] [f `(get ~v ~(key-of f))]) fields)
                 ~self ~v]
             (loop [~@(interleave args gs)] ~@body))
           (~refuse ~v))))))

(defn check-method-sections!
  "Refuses a protocol implemented twice, or an interface listed twice, among `method-secs`."
  [ctx method-secs]
  (when-let [[_ s] (first (for [[h n] (frequencies (map #(or (:protocol %) (:class %)) method-secs))
                                :when (> n 1)]
                            [h (some #(when (= h (or (:protocol %) (:class %))) %) method-secs)]))]
    (fail! ctx (if (:protocol s)
                 (str "protocol " (:marker s) " is implemented twice")
                 (str "interface " (:marker s) " is listed twice")))))

(defn check-methods!
  "Refuses a method written twice with one signature, and a method that hints `tname` or
  `classname`: the type's class does not exist while the methods compile."
  [ctx tname classname methods]
  (doseq [[sig c] (frequencies (map :sig methods)) :when (> c 1)
          :let [{:keys [name marker params line]} (some #(when (= sig (:sig %)) %) methods)
                n (count params)]]
    (fail! (assoc ctx :line line)
           (str "method " name " of " marker " is written twice with " n (parameters n))))
  (doseq [{:keys [name marker params body line]} methods]
    (when-let [f (hints-own-class tname classname (cons params body))]
      (fail! (assoc ctx :line line)
             (str "method " name " of " marker " hints " tname " on " (pr-str f) ": " tname
                  " has no class while the methods compile. In a method body " tname
                  " is the value's class, (class this), and takes no hint")))))
