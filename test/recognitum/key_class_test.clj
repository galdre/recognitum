(ns recognitum.key-class-test
  "The key-class strategy's definitions: the interfaces a value implements, the functions its
  methods call, and the definitions it refuses."
  (:require
   [clojure.edn :as edn]
   [clojure.test :refer [deftest is testing]]
   [recognitum.proof :as proof]
   [recognitum.proof.key-class :as key-class]))

(definterface Prims
  (^int add [^int a ^long b ^double c ^boolean d ^char e])
  (^void note [x])
  (^long wide [a b c d e f g h i j k l m n o p q r s t u])
  (twenty [a b c d e f g h i j k l m n o p q r s t]))

(definterface Plain (show []))

(definterface Assocs (assoc$0 [x]))

(definterface ReturnsString (^String same []))
(definterface ReturnsLong (^Long same []))

(defprotocol Named (label [v]))

(def ^:private noted (atom nil))

(def ^:private definition
  {:interfaces [Prims Plain recognitum.key_class_test.Named clojure.lang.IDeref Object]
   :methods    {'[add 5]      (fn [_ a b c d e] (reset! noted [a b c d e]) 42)
                '[note 1]     (fn [_ x] (reset! noted x) :ignored)
                '[wide 21]    (fn [& xs] (count xs))
                '[twenty 20]  (fn [v & xs] [v xs])
                '[show 0]     (fn [v] [:show v])
                '[label 0]    (fn [v] (:n v))
                '[toString 0] (fn [v] (str "n=" (:n v)))}})

(defn- define [d] (proof/define-type key-class/strategy nil d))

(defn- refusal' [type-name d]
  (let [answer (proof/refusal key-class/strategy d)
        thrown (try (proof/define-type key-class/strategy type-name d) nil
                    (catch clojure.lang.ExceptionInfo e e))]
    (is (= answer (ex-data thrown)) "the definition refuses exactly what refusal answers")
    (some-> thrown ex-message)))

(defn- refusal [d] (refusal' nil d))

(deftest methods-call-their-functions-with-the-value
  (let [h (define definition)
        v (proof/seal h {:n 1})]
    (is (= 42 (.add ^recognitum.key_class_test.Prims v 1 2 3.0 true \c)))
    (is (= [1 2 3.0 true \c] @noted) "primitive arguments arrive boxed")
    (is (nil? (.note ^recognitum.key_class_test.Prims v :x)))
    (is (= :x @noted))
    (is (= 22 (.wide ^recognitum.key_class_test.Prims v 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21))
        "the value and 21 arguments, through applyTo")
    (let [[self args] (.twenty ^recognitum.key_class_test.Prims v 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20)]
      (is (identical? v self))
      (is (= (range 1 21) args) "the value and 20 arguments, through applyTo"))
    (is (identical? v (second (.show ^recognitum.key_class_test.Plain v))))
    (is (= 1 (label v)) "a protocol placed through its interface")
    (is (thrown? UnsupportedOperationException (deref v)) "a listed method with no function throws")
    (is (= "n=1" (str v)))
    (testing "drafts implement none of the interfaces"
      (is (not-any? #(instance? % (proof/open h)) [Prims Plain recognitum.key_class_test.Named])))))

(deftest printing-shows-the-map
  (let [v (proof/seal (define definition) {:n 1})]
    (is (= {:n 1} (edn/read-string (pr-str v))) "IDeref's print entry does not take over")
    (is (= {:n 1} (binding [*read-eval* true] (read-string (binding [*print-dup* true] (pr-str v))))))))

(deftest values-keep-their-definitions-methods
  (let [old (proof/seal (define definition) {:n 1})
        new (proof/seal (define (assoc-in definition [:methods '[show 0]] (fn [_] :new))) {:n 1})]
    (is (= :show (first (.show ^recognitum.key_class_test.Plain old))))
    (is (= :new (.show ^recognitum.key_class_test.Plain new)))))

(defmacro ^:private are-refused [& pairs]
  `(do ~@(for [[d msg] (partition 2 pairs)]
           `(is (some-> (refusal ~d) (.contains ~msg)) ~(pr-str d)))))

(deftest refused-definitions
  (are-refused
   {:interfaces [String]}                                          "not an interface"
   {:interfaces [Plain] :methods {'[hide 0] identity}}              "no listed interface declares"
   {:interfaces [Prims] :methods {'[add 4] identity}}               "no listed interface declares"
   {:interfaces [java.util.Map] :methods {'[get 1] identity}}       "without the definition"
   {:interfaces [Object] :methods {'[equals 1] identity}}           "equality"
   {:interfaces [Object] :methods {'[hashCode 0] identity}}         "equality"
   {:interfaces [] :methods {'[toString 0] identity}}               "no listed interface declares"
   {:interfaces [Plain] :methods {'[show 0] identity ['show []] identity}} "two signatures"
   {:interfaces [Plain] :methods {'[show 0] 7}}                     "not a function"
   {:interfaces [java.util.function.Consumer java.util.function.IntConsumer]
    :methods {'[accept 1] identity}}                                "more than one method"))

(deftest refusals-are-data-and-the-definition-throws-them
  (let [r #(dissoc (proof/refusal key-class/strategy %) :message)]
    (is (nil? (proof/refusal key-class/strategy definition)))
    (is (nil? (proof/refusal key-class/strategy nil)))
    (is (= {:kind :undeclared :method '[hide 0]} (r {:interfaces [Plain] :methods {'[hide 0] identity}})))
    (is (= {:kind :ambiguous :method '[accept 1]}
           (r {:interfaces [java.util.function.Consumer java.util.function.IntConsumer] :methods {'[accept 1] identity}})))
    (is (= {:kind :equality :method '[equals 1]} (r {:interfaces [Object] :methods {'[equals 1] identity}})))
    (is (= {:kind :equality :method '[hashCode 0]} (r {:interfaces [Object] :methods {['hashCode []] identity}})))
    (is (= {:kind :map-method :method '[get 1]} (r {:interfaces [java.util.Map] :methods {'[get 1] identity}})))
    (is (= {:kind :clash :method '[forEachRemaining 1] :interfaces [java.util.Iterator java.util.Spliterator]}
           (update (r {:interfaces [java.util.Iterator java.util.Spliterator]}) :interfaces (partial sort-by #(.getName ^Class %)))))
    (is (= {:kind :clash :method '[same 0] :interfaces [ReturnsString ReturnsLong]}
           (r {:interfaces [ReturnsString ReturnsLong]})))
    (is (= {:kind :not-an-interface :interfaces [String]} (r {:interfaces [String]})))
    (is (= {:kind :draft-interface :interfaces [java.util.function.Predicate]} (r {:interfaces [java.util.function.Predicate]})))
    (is (= {:kind :duplicate :method '[show 0]} (r {:interfaces [Plain] :methods (array-map '[show 0] identity ['show []] identity)})))
    (is (= {:kind :not-a-function :method '[show 0]} (r {:interfaces [Plain] :methods {'[show 0] 7}})))
    (is (= :malformed (:kind (r {:interfaces [Plain] :methods {'[show] identity}})))))
  (testing "the definition throws the answer, as data and message"
    (let [d {:interfaces [Plain] :methods {'[hide 0] identity}}
          e (try (define d) nil (catch clojure.lang.ExceptionInfo e e))]
      (is (= (proof/refusal key-class/strategy d) (ex-data e)))
      (is (= "refused definition: no listed interface declares: [hide 0]" (ex-message e))))))

(deftest the-class-name-comes-from-the-strategy
  (is (= "recognitum.key_class_test.Named_Thing" (proof/class-name key-class/strategy 'recognitum.key-class-test/Named-Thing)))
  (is (nil? (proof/class-name key-class/strategy nil)))
  (dotimes [_ 2]
    (let [[vc] (proof/classes (proof/define-type key-class/strategy 'recognitum.key-class-test/Named-Thing {:interfaces [Plain]}))]
      (is (= (proof/class-name key-class/strategy 'recognitum.key-class-test/Named-Thing) (.getName ^Class vc))))))

(deftest the-constructor-names-the-class-and-the-engine
  (let [[vc] (proof/classes (proof/define-type key-class/strategy 'recognitum.key-class-test/Thing))
        msg  (try (clojure.lang.Reflector/invokeConstructor vc (object-array [nil {}])) nil
                  (catch SecurityException e (.getMessage e)))]
    (is (= (str "recognitum.key_class_test.Thing's constructor takes a key only recognitum holds: "
                "a value of this type is made only through recognitum")
           msg))
    (is (not (.contains ^String msg "map->")))))

(deftest default-methods
  (let [then #(.apply (.andThen ^java.util.function.Function % (reify java.util.function.Function (apply [_ r] r))) :x)]
    (testing "a default with no function keeps its body, which calls the abstract method"
      (let [given (proof/seal (define {:interfaces [java.util.function.Function] :methods {'[apply 1] (fn [_ x] [:applied x])}}) {})
            none  (proof/seal (define {:interfaces [java.util.function.Function]}) {})]
        (is (= [:applied :x] (then given)))
        (is (thrown? UnsupportedOperationException (then none)) "an abstract method with no function throws")))
    (testing "a function replaces a default body"
      (let [v (proof/seal (define {:interfaces [java.util.function.Function]
                                   :methods {'[apply 1] (fn [_ x] x) '[andThen 1] (fn [_ g] (reify java.util.function.Function (apply [_ _] :replaced)))}})
                          {})]
        (is (= :replaced (.apply (.andThen ^java.util.function.Function v (reify java.util.function.Function (apply [_ r] r))) :x)))))
    (testing "two unrelated defaults of one method"
      (is (some-> (refusal {:interfaces [java.util.Iterator java.util.Spliterator]})
                  (.contains "give default bodies of forEachRemaining and the definition gives no function for it")))
      (let [v (proof/seal (define {:interfaces [java.util.Iterator java.util.Spliterator]
                                   :methods {'[forEachRemaining 1] (fn [_ _] nil)}})
                          {})]
        (is (nil? (.forEachRemaining ^java.util.Iterator v nil)) "a function settles which body runs")))
    (testing "the most specific declaration decides: ListIterator makes Iterator's default remove abstract"
      (doseq [ifaces [[java.util.Iterator java.util.ListIterator] [java.util.ListIterator java.util.Iterator]]]
        (let [v (proof/seal (define {:interfaces ifaces}) {})]
          (is (= "no function implements remove"
                 (try (.remove ^java.util.Iterator v) nil (catch UnsupportedOperationException e (.getMessage e))))
              (pr-str ifaces)))))))

(defn- default-interface
  "Defines an interface named `n` whose one method `m`, of descriptor `desc` returning void
  or int, has a default body."
  [^String n ^String m ^String desc]
  (let [cw (clojure.asm.ClassWriter. clojure.asm.ClassWriter/COMPUTE_FRAMES)
        t  (.replace n \. \/)]
    (.visit cw clojure.asm.Opcodes/V1_8
            (bit-or clojure.asm.Opcodes/ACC_PUBLIC clojure.asm.Opcodes/ACC_INTERFACE clojure.asm.Opcodes/ACC_ABSTRACT)
            t nil "java/lang/Object" nil)
    (doto (.visitMethod cw clojure.asm.Opcodes/ACC_PUBLIC m desc nil nil)
      (.visitCode)
      (cond-> (.endsWith desc "I") (.visitInsn clojure.asm.Opcodes/ICONST_0))
      (.visitInsn (if (.endsWith desc "I") clojure.asm.Opcodes/IRETURN clojure.asm.Opcodes/RETURN))
      (.visitMaxs 0 0)
      (.visitEnd))
    (.visitEnd cw)
    (.defineClass (clojure.lang.DynamicClassLoader.) n (.toByteArray cw) nil)))

(deftest defaults-meet-the-maps-own-methods
  (testing "a listed default and an unrelated default of the map's interfaces conflict"
    (let [i (default-interface "recognitum.key_class_test.ForEachPair" "forEach" "(Ljava/util/function/BiConsumer;)V")]
      (is (some-> (refusal {:interfaces [i]}) (.contains "java.util.Map")))))
  (testing "a method the value's class declares wins over every default"
    (let [a (default-interface "recognitum.key_class_test.CountA" "count" "()I")
          b (default-interface "recognitum.key_class_test.CountB" "count" "()I")
          v (proof/seal (define {:interfaces [a b]}) {:x 1 :y 2})]
      (is (= 2 (count v))))))

(definterface NarrowMap
  (^recognitum.key_class_test.NarrowMap without [k]))

(deftest map-methods-are-set-aside-before-return-types
  (is (some? (define {:interfaces [clojure.lang.IPersistentMap]})))
  (is (some? (define {:interfaces [recognitum.key_class_test.NarrowMap]}))))

(definterface Outranked (o []))

(deftest an-outranking-print-entry-refuses-the-definition
  (.addMethod ^clojure.lang.MultiFn print-method recognitum.key_class_test.Outranked (fn [_ ^java.io.Writer w] (.write w "outranked")))
  (try
    (prefer-method print-method recognitum.key_class_test.Outranked clojure.lang.IPersistentMap)
    (let [before [(prefers print-method) (prefers print-dup)]
          msg    (refusal {:interfaces [recognitum.key_class_test.Outranked]})]
      (is (= {:kind :clash :interfaces [recognitum.key_class_test.Outranked]}
             (dissoc (proof/refusal key-class/strategy {:interfaces [recognitum.key_class_test.Outranked]}) :message)))
      (is (= (str "refused definition: print-method prefers this interface's entry to the map's, so a value "
                  "could not print as its map: recognitum.key_class_test.Outranked")
             msg))
      (is (= before [(prefers print-method) (prefers print-dup)]) "a refusal sets no preference"))
    (finally (remove-method print-method recognitum.key_class_test.Outranked))))

(defmacro ^:private many-methods
  "An interface named `nm` with methods m0 ... m(n-1), none taking arguments."
  [nm n]
  `(definterface ~nm ~@(for [i (range n)] (list (symbol (str "m" i)) []))))

(many-methods Many 130)

(deftest a-definition-with-more-than-127-methods
  (let [v (proof/seal (define {:interfaces [Many] :methods {'[m129 0] (fn [_] :last) '[m0 0] (fn [_] :first)}}) {})]
    (is (= :last (.m129 ^recognitum.key_class_test.Many v)))
    (is (= :first (.m0 ^recognitum.key_class_test.Many v)))
    (is (= (repeat 128 UnsupportedOperationException)
           (for [i (range 1 129)]
             (try (clojure.lang.Reflector/invokeInstanceMethod v (str "m" i) (object-array 0)) nil
                  (catch Throwable t (class t)))))
        "each method with no function throws, whatever its place in the table")))

(defn- clone [x]
  (let [bo (java.io.ByteArrayOutputStream.)]
    (with-open [o (java.io.ObjectOutputStream. bo)] (.writeObject o x))
    (with-open [i (java.io.ObjectInputStream. (java.io.ByteArrayInputStream. (.toByteArray bo)))]
      (.readObject i))))

(deftest changes-of-a-value-of-a-new-type
  (let [h (define {:interfaces [java.util.Map]})
        v (proof/seal h (with-meta {:a 1 :b 2} {:m true}))]
    (testing "a change that changes nothing returns the value"
      (is (identical? v (assoc v :a 1)))
      (is (identical? v (dissoc v :z)))
      (is (identical? v (conj v [:a 1]))))
    (testing "with no write installed, a change is a plain map with the value's meta"
      (doseq [w [(assoc v :a 2) (dissoc v :a) (conj v [:c 3])]]
        (is (not (proof/proven? h w)))
        (is (instance? clojure.lang.PersistentArrayMap w))
        (is (= {:m true} (meta w)))))
    (testing "a listed interface that the map already implements keeps the map's methods"
      (is (= 1 (.get ^java.util.Map v :a)))
      (is (= 2 (.size ^java.util.Map v))))
    (testing "serialization yields the plain map"
      (let [c (clone v)]
        (is (= {:a 1 :b 2} c))
        (is (not (proof/proven? h c)))))))

(deftest a-transient-of-a-value-makes-one-checked-write
  (let [h       (define nil)
        written (atom [])
        _       (proof/install-write! h (fn [old entries] (swap! written conj entries) (proof/seal h entries)))
        v       (proof/seal h {:a 1})]
    (testing "into with more entries than an array map holds"
      (let [big (zipmap (range 20) (range 20))
            w   (into v big)]
        (is (= (merge {:a 1} big) w))
        (is (proof/proven? h w))
        (is (= 1 (count @written)))))
    (testing "dissoc! and find on the transient"
      (let [t (transient v)]
        (is (= [:a 1] (find t :a)))
        (is (nil? (find t :z)))
        (is (= {} (persistent! (dissoc! t :a))))
        (is (thrown? IllegalAccessError (assoc! t :b 2)) "a transient is spent by persistent!")))))

(deftest refused-shapes
  (are-refused
   {:interfaces [:not-a-class]}                                     "not {:interfaces"
   {:interfaces [Plain] :methods {'[show] identity}}                "a signature is"
   {:interfaces [Plain] :methods {'[show :x] identity}}             "a signature is"
   {:interfaces [Plain] :methods {['show [:x]] identity}}           "a signature is"))


(deftest refused-return-type-conflicts
  (are-refused
   {:interfaces [ReturnsString ReturnsLong]}                        "differ only in return type"))

(deftest a-definition-without-print-entries-adds-no-preferences
  (let [before (prefers print-method)]
    (define {:interfaces [Plain]})
    (is (= before (prefers print-method)))
    (is (not-any? (set (get (prefers print-method) clojure.lang.IPersistentMap))
                  [Object clojure.lang.IPersistentCollection java.util.Collection])
        "the map's entry is preferred only to entries of listed interfaces' supertypes")))

(gen-interface :name recognitum.key_class_test.SubBiConsumer :extends [java.util.function.BiConsumer])

(deftest drafts-implement-no-listed-interface
  (are-refused
   {:interfaces [java.util.function.BiConsumer]}                    "a draft implements this interface"
   {:interfaces [java.util.function.Predicate]}                     "a draft implements this interface"))

(deftest mark-hands-the-key-only-to-a-draft-of-its-type
  (let [h    (define nil)
        seen (atom [])
        spy  (reify java.util.function.BiConsumer (accept [_ k c] (swap! seen conj k)))
        sub  (proof/seal (define {:interfaces [recognitum.key_class_test.SubBiConsumer]
                                  :methods {'[accept 2] (fn [_ k c] (swap! seen conj k))}})
                         {})
        other (proof/open (define nil))]
    (doseq [x [spy sub other {} nil]]
      (is (thrown? IllegalArgumentException (proof/mark! h x :c)) (pr-str (class x))))
    (is (instance? java.util.function.BiConsumer sub))
    (is (empty? @seen) "no object other than the type's own draft is handed the key")))

(deftest a-refused-definition-leaves-no-class-under-its-name
  (let [def! #(binding [*ns* (the-ns 'recognitum.key-class-test)] (eval '(definterface Redefined (r []))))
        old  (def!)
        _    (def!)
        name "recognitum.key_class_test.Stray"]
    (is (not (identical? old (Class/forName "recognitum.key_class_test.Redefined" false (clojure.lang.DynamicClassLoader.))))
        "the interface was defined again")
    (is (some-> (refusal' 'recognitum.key-class-test/Stray {:interfaces [old]}) (.contains "now names another class")))
    (is (= {:kind :reloaded-interface :interfaces [old]} (dissoc (proof/refusal key-class/strategy {:interfaces [old]}) :message)))
    (is (nil? (try (Class/forName name false (clojure.lang.DynamicClassLoader.)) (catch ClassNotFoundException _ nil))))))

(deftype Imitation$Draft [] java.util.function.Predicate (test [_ _] true))

(deftest marked?-reads-the-marks-of-the-strategys-own-drafts
  (let [tname 'recognitum.key-class-test/Marked
        h     (proof/define-type key-class/strategy tname)
        d     (proof/open h)
        oh    (define nil)
        other (proof/open oh)
        m?    #(proof/marked? key-class/strategy %1 %2)]
    (is (false? (m? d :c)))
    (proof/mark! h d :c)
    (proof/mark! oh other :o)
    (is (true? (m? d :c)))
    (is (false? (m? d :e)))
    (is (true? (m? other :o)) "a draft of another type answers its own marks")
    (proof/define-type key-class/strategy tname)
    (is (true? (m? d :c)) "a draft of an earlier definition answers the same")
    (testing "anything that is not a draft the strategy made answers false"
      (doseq [x [(Imitation$Draft.) (reify java.util.function.Predicate (test [_ _] true))
                 (proof/seal h {:c true}) {:c true} #{:c} nil]]
        (is (false? (m? x :c)) (pr-str (class x)))))))

(deftest the-refused-method-is-named-as-the-signature-spells-it
  (let [r #(:method (proof/refusal key-class/strategy {:interfaces [Plain] :methods {% identity}}))]
    (is (= '[hide-it 0] (r '[hide-it 0])))
    (is (= '[hide_it 0] (r ["hide_it" 0])))
    (is (= '[my.ns/show 0] (r '[my.ns/show 0])) "a qualified name names no method")
    (is (nil? (r ["show" 0])))))

(deftest a-refusal-depends-on-no-function
  (let [d     {:interfaces [:not-a-class] :methods {'[show 0] (fn [_] 1)}}
        blank {:interfaces [:not-a-class] :methods {'[show 0] (fn [& _])}}]
    (is (= (proof/refusal key-class/strategy d) (proof/refusal key-class/strategy blank)))))

(deftest a-type-is-named-by-a-symbol
  (doseq [n [:a.b/T "a.b/T"]]
    (is (thrown? IllegalArgumentException (proof/class-name key-class/strategy n)) (pr-str n))))

(deftest a-value-keeps-its-declared-keys-in-fields
  (let [h (define {:keys [:a :n/b]})
        v (proof/seal h (with-meta {:a 1 :n/b nil :x 2} {:m 1}))
        w (proof/seal h {:x 2})
        c (class v)]
    (is (= #{"f0" "f1"} (set (for [^java.lang.reflect.Field f (.getDeclaredFields c)
                                   :when (re-matches #"f\d+" (.getName f))]
                               (.getName f))))
        "one field per declared key")
    (testing "a value answers as the plain map of its entries"
      (is (= {:a 1 :n/b nil :x 2} v))
      (is (= (hash {:a 1 :n/b nil :x 2}) (hash v)))
      (is (= {:m 1} (meta v)))
      (is (= 3 (count v)))
      (is (nil? (get v :n/b :none)) "nil under a declared key is an entry")
      (is (contains? v :n/b))
      (is (= :none (get w :a :none)) "an absent declared key is no entry")
      (is (not (contains? w :a)))
      (is (nil? (find w :a)))
      (is (= 1 (count w)))
      (is (= [[:a 1] [:n/b nil] [:x 2]] (vec (seq v))) "the declared keys first, in order"))
    (testing "with no write installed, a change is a plain map"
      (is (= {:x 2 :a 5} (assoc w :a 5)))
      (is (instance? clojure.lang.PersistentArrayMap (dissoc v :a)))
      (is (= {:m 1} (meta (dissoc v :a))))
      (is (identical? v (assoc v :a 1)))
      (is (identical? w (dissoc w :a)))
      (is (identical? v (dissoc v :z))))
    (is (= {:a 1 :n/b nil :x 2} (clone v)) "serialization yields the plain map")
    (is (= {:x 2} (proof/seal h (dissoc v :a :n/b))) "a seal of a map with no declared key")))

(deftest keys-are-distinct-keywords
  (are-refused
   {:keys [:a :a]}                                                  "the keys are distinct keywords"
   {:keys ['a]}                                                     "the keys are distinct keywords"
   {:keys :a}                                                       "the keys are distinct keywords"))

(deftest assoc-and-dissoc-name-the-key-they-write
  (let [h     (define {:keys [:a]})
        calls (atom [])
        _     (proof/install-write! h (fn ([old entries] (swap! calls conj [2 entries]) (proof/seal h entries))
                                        ([old entries k v] (swap! calls conj [4 k v entries]) (proof/seal h entries))))
        v     (proof/seal h {:a 1 :x 2})
        gone  (proof/removed key-class/strategy)]
    (is (proof/proven? h (assoc v :a 3)))
    (is (proof/proven? h (assoc v :x 3)))
    (is (proof/proven? h (dissoc v :a)))
    (is (proof/proven? h (dissoc v :x)))
    (is (proof/proven? h (merge v {:a 5})))
    (is (= [[4 :a 3 {:a 3 :x 2}] [4 :x 3 {:a 1 :x 3}] [4 :a gone {:x 2}] [4 :x gone {:a 1}] [2 {:a 5 :x 2}]]
           @calls))
    (is (identical? gone (proof/removed key-class/strategy)) "one marker")
    (let [gate (proof/installed key-class/strategy (class v))]
      (is (thrown? clojure.lang.ArityException (gate v {:a 9 :x 9} :a 9))
          "the keyless gate has no four-argument arity: the key it names would be a caller's word"))))

(deftest a-write-with-no-four-argument-arity-refuses-a-one-key-change
  (let [h     (define {:keys [:a]})
        calls (atom [])
        _     (proof/install-write! h (fn [old entries] (swap! calls conj entries) (proof/seal h entries)))
        v     (proof/seal h {:a 1})]
    (is (thrown? clojure.lang.ArityException (assoc v :a 2)))
    (is (thrown? clojure.lang.ArityException (dissoc v :a)))
    (is (proof/proven? h (merge v {:a 3})) "a change of the whole map still calls two")
    (is (= [{:a 3}] @calls))))

(deftest a-keywords-lookup-of-a-declared-key-reads-its-field
  (let [h    (define {:keys [:a :n/b]})
        v    (proof/seal h {:a 1 :x 2})
        w    (proof/seal h {:n/b nil})
        ;; compiled here, so the call sites hold no thunk from an earlier run
        look (eval '(fn [m] [(:a m) (:n/b m) (:x m)]))]
    (is (instance? clojure.lang.IKeywordLookup v) "a declared key's lookup reads through a thunk")
    (is (not (instance? clojure.lang.IKeywordLookup (proof/seal (define nil) {}))) "and with no keys, none")
    (is (= [1 nil 2] (look v)))
    (is (= [nil nil nil] (look w)) "absent and nil alike read nil")
    (is (= [3 4 5] (look {:a 3 :n/b 4 :x 5})) "the same call sites, on another class")
    (is (= [1 nil 2] (look v)) "and on the value again")))

(deftest assocEx-makes-one-checked-write
  (let [h     (define {:keys [:a]})
        calls (atom [])
        _     (proof/install-write! h (fn ([_ e] (swap! calls conj e) (proof/seal h e))
                                        ([_ e k v] (swap! calls conj [k v e]) (proof/seal h e))))
        v     (proof/seal h {:a 1})
        w     (.assocEx ^clojure.lang.IPersistentMap v :z 2)]
    (is (= {:a 1 :z 2} w))
    (is (proof/proven? h w))
    (is (= [{:a 1 :z 2}] @calls))
    (is (thrown? RuntimeException (.assocEx ^clojure.lang.IPersistentMap v :a 2)))))

(deftest a-variadic-write-is-told-the-key-where-it-takes-four-arguments
  (let [h     (define {:keys [:a]})
        calls (atom [])
        _     (proof/install-write! h (fn ([_ e] (swap! calls conj 2) (proof/seal h e))
                                        ([_ e _ _ & _] (swap! calls conj 4) (proof/seal h e))))
        v     (proof/seal h {:a 1})]
    (is (proof/proven? h (assoc v :a 2)))
    (is (= [4] @calls)))
  (let [h     (define {:keys [:a]})
        _     (proof/install-write! h (fn ([_ e] (proof/seal h e))
                                        ([_ e _ _ _ & _] (proof/seal h e))))
        v     (proof/seal h {:a 1})]
    (is (thrown? clojure.lang.ArityException (assoc v :a 2)) "one that needs five takes no four")))

(deftest the-keyless-gate-starts-only-from-a-value-of-its-definition
  (let [h (define {:keys [:a]})
        _ (proof/install-write! h (fn [_ e] (proof/seal h e)))
        g (proof/installed key-class/strategy (first (proof/classes h)))
        v (proof/seal h {:a 1})]
    (is (thrown? IllegalArgumentException (g nil {:a 2})))
    (is (thrown? IllegalArgumentException (g {:a 1} {:a 2})))
    (is (thrown? IllegalArgumentException (g {:a 1})))
    (is (proof/proven? h (g v {:a 2})))))

(deftest a-guarded-assoc-calls-its-guard-and-not-the-write
  (let [h      (define {:keys [:a :b]})
        calls  (atom [])
        asked  (atom [])
        write  (fn ([_ e] (swap! calls conj [2 e]) (proof/seal h e))
                 ([_ e k v] (swap! calls conj [4 k v e]) (proof/seal h e)))
        _      (proof/install-write! h write (fn [k] (swap! asked conj k)
                                               (when (= k :a)
                                                 (fn [old v] (swap! calls conj [:guard (into {} old) v])
                                                   (when (= v :bad) (throw (ex-info "refused" {:v v})))
                                                   :ignored))))
        v      (proof/seal h (with-meta {:b 1 :x 2} {:m 1}))
        w      (assoc v :a 3)]
    (is (= [:a :b] @asked) "each declared key once, in order")
    (is (= [[:guard {:b 1 :x 2} 3]] @calls) "the guard alone, given the old value and v")
    (is (proof/proven? h w))
    (is (= {:a 3 :b 1 :x 2} w))
    (is (= {:m 1} (meta w)))
    (is (= 3 (count w)) "the absent key is now present")
    (is (identical? w (assoc w :a 3)) "an assoc that changes nothing calls nothing")
    (is (= 1 (count @calls)))
    (reset! calls [])
    (is (= {:v :bad} (ex-data (try (assoc v :a :bad) (catch clojure.lang.ExceptionInfo e e)))) "the guard's throw propagates")
    (is (= [[:guard {:b 1 :x 2} :bad]] @calls))
    (reset! calls [])
    (assoc v :b 5) (assoc v :x 5) (dissoc v :b) (merge v {:a 7}) (into v {:a 8}) (conj v [:a 9])
    (is (= [[4 :b 5 {:b 5 :x 2}] [4 :x 5 {:b 1 :x 5}] [4 :b (proof/removed key-class/strategy) {:x 2}]
            [2 {:a 7 :b 1 :x 2}] [2 {:a 8 :b 1 :x 2}] [2 {:a 9 :b 1 :x 2}]]
           @calls)
        "an unguarded key, an undeclared key, dissoc, merge, into and conj call the write")))

(deftest a-guarded-install-is-the-one-install
  (let [h     (define {:keys [:a]})
        asked (atom 0)
        kw    (fn [_] (swap! asked inc) nil)
        write (fn [_ e] (proof/seal h e))]
    (doseq [g ["not a function" :a {:a 1} #{:a} #'clojure.core/identity]]
      (is (thrown? IllegalArgumentException (proof/install-write! h write (constantly g)))
          "a guard is made by fn: a keyword, a map, a set or a var would return, and so permit, for any write"))
    (is (nil? (proof/installed key-class/strategy (first (proof/classes h)))) "a refused install installs nothing")
    (proof/install-write! h write kw)
    (is (= 1 @asked))
    (is (thrown? SecurityException (proof/install-write! h write kw)))
    (is (proof/proven? h (merge (proof/seal h {:a 1}) {:a 2})) "after the refused installs, this one installed")
    (is (thrown? Exception (proof/install-write! h write)))
    (is (= 1 @asked) "a second install asks the key write nothing"))
  (let [h (define {:keys [:a]})]
    (proof/install-write! h (fn [_ e] (proof/seal h e)))
    (is (thrown? SecurityException (proof/install-write! h (fn [_ e] e) (constantly (fn [_ _] nil))))
        "nor after an install without guards")))

(deftest a-value-calls-its-own-definitions-guard
  (let [n     (symbol "recognitum.key-class-test" (name (gensym "G")))
        log   (atom [])
        guard (fn [tag] (fn [k] (fn [_ v] (swap! log conj [tag k v]))))
        h1    (proof/define-type key-class/strategy n {:keys [:a]})
        _     (proof/install-write! h1 (fn [_ e] (proof/seal h1 e)) (guard :one))
        v1    (proof/seal h1 {:a 1})
        h2    (proof/define-type key-class/strategy n {:keys [:a]})
        _     (proof/install-write! h2 (fn [_ e] (proof/seal h2 e)) (guard :two))
        v2    (proof/seal h2 {:a 1})]
    (is (proof/proven? h1 (assoc v1 :a 2)))
    (is (not (proof/proven? h2 (assoc v1 :a 2))))
    (is (proof/proven? h2 (assoc v2 :a 2)))
    (is (= [[:one :a 2] [:one :a 2] [:two :a 2]] @log))))

(deftest the-guarded-shape-adds-no-keyless-way-in
  (let [h  (define {:keys [:a]})
        c  (first (proof/classes h))
        install (.getMethod ^Class c "install" (into-array Class [Object Object Object (class (object-array 0)) Object]))]
    (is (= 1 (count (.getConstructors ^Class c))) "the constructor that copies a value with one field set is private")
    (doseq [k [nil (Object.)]]
      (is (thrown? SecurityException
                   (try (.invoke install nil (object-array [k (fn [_ e] e) (fn [_ e] e) (object-array [(fn [_ _] nil)]) (fn [_ o] o)]))
                        (catch java.lang.reflect.InvocationTargetException e (throw (.getCause e)))))))
    (is (nil? (proof/installed key-class/strategy c)) "nothing was installed")
    (is (thrown? NoSuchFieldException (.getField ^Class c "G0")) "the guards are private")))

(deftest seq-and-equality-read-the-fields
  (let [ks    (mapv #(keyword (str "k" %)) (range 12))
        h     (define {:keys ks})
        other (define {:keys ks})
        maps  [(zipmap ks (range)) (dissoc (zipmap ks (range)) :k3) (assoc (zipmap ks (range)) :k3 nil)
               (assoc (zipmap ks (range)) :x 1) (assoc (zipmap ks (range)) :x 2) {:k0 [1 2]} {:k0 '(1 2)} {}
               {:k0 1} {:k0 1.0} {:k0 (int 1)}]
        vs    (mapv #(proof/seal h %) maps)]
    (testing "seq gives the declared keys' entries in their order, then the others"
      (is (= (conj ks :x) (map key (seq (vs 3)))))
      (is (nil? (seq (vs 7))))
      (is (= (seq (vs 3)) (iterator-seq (.iterator ^Iterable (vs 3))))))
    (doseq [i (range (count maps)) j (range (count maps))
            :let [m (maps i) n (maps j) v (vs i) w (vs j)]]
      (testing [m n]
        (is (= (= m n) (= v w) (= v n)) "= of two values answers as of their maps")
        (is (= (.equals ^Object m n) (.equals ^Object v w) (.equals ^Object v n)) "equals too")
        (when (= v w) (is (= (hash v) (hash w))))))
    (is (= (vs 0) (proof/seal other (maps 0))) "a value of another class with the same entries")))

(deftest reduce-and-reduce-kv-read-the-fields
  (let [ks (mapv #(keyword (str "k" %)) (range 12))
        h  (define {:keys ks})
        m  (-> (zipmap ks (range)) (dissoc :k3) (assoc :x 100 :y 200))
        v  (proof/seal h m)]
    (is (instance? clojure.lang.IReduceInit v))
    (is (instance? clojure.lang.IKVReduce v))
    (is (= (reduce + (vals m)) (reduce-kv (fn [a _ x] (+ a x)) 0 v)) "every entry, ext's too")
    (is (= (set m) (set (reduce conj [] v))))
    (is (= m (into {} v)))
    (let [walked (reduce-kv (fn [a k _] (conj a k)) [] v)]
      (is (= (remove #{:k3} ks) (take 11 walked)) "the declared keys in their order")
      (is (= #{:x :y} (set (drop 11 walked))) "then the others"))
    (testing "a reduced stops the walk, in the fields and in ext"
      (is (= :k1 (reduce-kv (fn [_ k _] (if (= k :k1) (reduced k) nil)) nil v)))
      (is (= :x (reduce-kv (fn [_ k _] (if (= k :x) (reduced k) nil)) nil v)))
      (is (= 2 (reduce (fn [n _] (if (= n 2) (reduced n) (inc n))) 0 v))))
    (is (= 7 (reduce-kv (fn [a _ _] (inc a)) 7 (proof/seal h {}))) "an empty value answers init")))

(definterface Folds (kvreduce [^clojure.lang.IFn f init]))

(deftest a-listed-kvreduce-forwards-to-its-function
  (let [v (proof/seal (define {:keys [:a] :interfaces [Folds] :methods {'[kvreduce 2] (fn [_ _ init] [:mine init])}})
                      {:a 1})]
    (is (= [:mine 0] (.kvreduce ^recognitum.key_class_test.Folds v + 0)))
    (is (= 1 (reduce (fn [a _] (inc a)) 0 v)) "reduce is still the value's own")))

(defn- change-guarded
  "A type of `ks` whose write, guard of `:a` and change guard log to `log`; the change guard
  refuses a `:b` of 0."
  [ks log]
  (let [h (define {:keys ks})]
    (proof/install-write! h
                          (fn ([_ e] (swap! log conj [:write e]) (proof/seal h e))
                            ([_ e k _] (swap! log conj [:write k]) (proof/seal h e)))
                          (fn [k] (when (= k :a) (fn [_ v] (swap! log conj [:guard v]))))
                          (fn [_ ch]
                            (swap! log conj [:changes (into {} ch)])
                            (when (= 0 (get ch :b)) (throw (ex-info "refused" {})))))
    h))

(deftest a-change-guard-is-told-only-the-net-change
  (doseq [ks [[:a :b] (into [:a :b] (map #(keyword (str "k" %)) (range 10)))]]
    (let [log (atom [])
          h   (change-guarded ks log)
          gone (proof/removed key-class/strategy)
          v   (proof/seal h (with-meta {:a 1 :b 2 :x 3} {:m 1}))
          changed (fn [f] (reset! log []) (let [r (f v)] [r @log]))]
      (testing (str (count ks) " declared keys")
        (is (= [{:a 5 :b 2 :x 3} [[:guard 5]]] (changed #(assoc % :a 5))) "a guarded key calls its guard")
        (is (= [{:a 1 :b 5 :x 3} [[:changes {:b 5}]]] (changed #(assoc % :b 5))))
        (is (= [{:a 1 :b 2 :x 3 :y 1} [[:changes {:y 1}]]] (changed #(assoc % :y 1))) "an undeclared key")
        (is (= [{:a 1 :x 3} [[:changes {:b gone}]]] (changed #(dissoc % :b))))
        (is (= [{:a 1 :b 2} [[:changes {:x gone}]]] (changed #(dissoc % :x))))
        (is (= [{:a 1 :b 2 :x 3 :q 1} [[:changes {:q 1}]]] (changed #(merge % {:b 2 :q 1}))) "an entry it already holds is no change")
        (is (= [{:a 1 :b 9 :x 3 :q 1} [[:changes {:b 9 :q 1}]]] (changed #(into % {:b 9 :q 1}))))
        (is (= [{:a 1 :b 7 :x 3} [[:changes {:b 7}]]] (changed #(conj % [:b 7]))))
        (is (thrown? IllegalArgumentException (conj v [:b 7 8])) "a vector conj'd is a pair, as on a map")
        (is (= [{:a 1 :b 6 :x 3 :q 7} [[:changes {:b 6 :q 7}]]]
               (changed #(conj % (list (clojure.lang.MapEntry/create :b 6) (clojure.lang.MapEntry/create :q 7)))))
            "of a seq of entries, each")
        (is (= [{:a 1 :b 7 :x 3} [[:changes {:b 7}]]] (changed #(conj % (list (clojure.lang.MapEntry/create :b 6) (clojure.lang.MapEntry/create :b 7)))))
            "of a seq of entries, the last of a key wins")
        (doseq [f [#(assoc % :b 2) #(dissoc % :zz) #(merge % {:b 2}) #(into % {:x 3}) #(conj % nil)
                   #(persistent! (-> (transient %) (assoc! :q 1) (dissoc! :q) (assoc! :b 3) (assoc! :b 2)))]]
          (let [[r calls] (changed f)]
            (is (identical? v r) "no change: the value itself")
            (is (= [] calls) "and nothing called")))
        (doseq [f [#(assoc % :b 5) #(dissoc % :x) #(merge % {:q 1}) #(into % {:q 1}) #(conj % [:q 1])]]
          (let [r (f v)]
            (is (proof/proven? h r))
            (is (= {:m 1} (meta r)) "the value's meta")))
        (reset! log [])
        (is (thrown? clojure.lang.ExceptionInfo (merge v {:b 0})) "the change guard's refusal propagates")
        (is (not-any? #(= :write (first %)) @log) "the write is not called")))))

(deftest a-transient-over-a-value-reads-as-one-over-its-map
  (let [h (change-guarded [:a :b] (atom []))
        v (proof/seal h {:a 1 :b 2 :x 3})
        ops [[:assoc :q 1] [:dissoc :a] [:assoc :b 2] [:dissoc :zz] [:assoc :a nil] [:dissoc :x] [:conj {:r 1 :q 2}]]
        run (fn [t] (reduce (fn [[t reads] [op k w]]
                              (let [t (case op :assoc (assoc! t k w) :dissoc (dissoc! t k) :conj (conj! t k))]
                                [t (conj reads (into [(count t)] (for [c [:a :b :x :q :r :zz]] [(get t c :none) (contains? t c) (find t c)])))]))
                            [t []] ops))
        [t1 r1] (run (transient {:a 1 :b 2 :x 3}))
        [t2 r2] (run (transient v))
        p2 (persistent! t2)]
    (is (= r1 r2))
    (is (= (persistent! t1) p2))
    (is (proof/proven? h p2))
    (is (thrown? IllegalAccessError (assoc! t2 :a 2)) "used after persistent!")
    (is (thrown? IllegalAccessError (count t2)))
    (is (thrown? IllegalArgumentException (conj (proof/seal h {:a 2}) (assoc! (transient v) :b 0)))
        "a transient's changes apply to the value it was made from alone")))

(deftest a-change-guard-install-is-the-one-install
  (let [h     (define {:keys [:a]})
        asked (atom 0)
        kw    (fn [_] (swap! asked inc) nil)
        write (fn [_ e] (proof/seal h e))]
    (doseq [cg ["not a function" :a {:a 1} #{:a} #'clojure.core/identity nil]]
      (is (thrown? IllegalArgumentException (proof/install-write! h write kw cg))))
    (is (= 0 @asked) "a refused change guard asks the key write nothing")
    (is (nil? (proof/installed key-class/strategy (first (proof/classes h)))) "and installs nothing")
    (proof/install-write! h write kw (fn [_ _] nil))
    (is (= 1 @asked))
    (doseq [f [#(proof/install-write! h write kw (fn [_ _] nil)) #(proof/install-write! h write kw) #(proof/install-write! h write)]]
      (is (thrown? Exception (f))))
    (is (= 1 @asked) "a second install asks the key write nothing")))

(deftest a-value-calls-its-own-definitions-change-guard
  (let [n   (symbol "recognitum.key-class-test" (name (gensym "C")))
        log (atom [])
        def! (fn [tag]
               (let [h (proof/define-type key-class/strategy n {:keys [:a]})]
                 (proof/install-write! h (fn [_ e] (proof/seal h e)) (constantly nil) (fn [_ ch] (swap! log conj [tag (into {} ch)])))
                 h))
        h1 (def! :one)
        v1 (proof/seal h1 {:a 1})
        h2 (def! :two)
        v2 (proof/seal h2 {:a 1})]
    (is (proof/proven? h1 (merge v1 {:a 2})))
    (is (not (proof/proven? h2 (merge v1 {:a 2}))))
    (is (proof/proven? h2 (merge v2 {:a 2})))
    (is (= [[:one {:a 2}] [:one {:a 2}] [:two {:a 2}]] @log))))

(deftest the-change-shape-adds-no-keyless-way-in
  (let [h (change-guarded [:a] (atom []))
        c (first (proof/classes h))]
    (is (= 1 (count (.getConstructors ^Class c))) "the constructor that applies a change is private")
    (is (thrown? NoSuchFieldException (.getField ^Class c "CHG")) "what the changes call is private")
    (is (empty? (.getConstructors (Class/forName (str (.getName ^Class c) "$I") false (.getClassLoader ^Class c))))
        "only T makes its iterator")
    (is (thrown? clojure.lang.ArityException ((proof/installed key-class/strategy c) (proof/seal h {:a 1}) {:b 1} :b 1))
        "the keyless gate reaches no change guard")))

(deftest iterators-and-count-answer-as-the-map
  (doseq [ks [[] [:a :b] (mapv #(keyword (str "k" %)) (range 12))]]
    (let [h (change-guarded ks (atom []))
          g (proof/define-type key-class/strategy nil {:keys ks})
          _ (proof/install-write! g (fn ([_ e] (proof/seal g e)) ([_ e _ _] (proof/seal g e)))
                                  (fn [k] (fn [_ _] nil)))
          ms [{} {:a 1} {:a nil :b 2 :x 3 "s" 4} (zipmap ks (range)) (assoc (zipmap ks (range)) :x 1)]
          its (fn [m] [(iterator-seq (.iterator ^Iterable m))
                       (iterator-seq (.keyIterator ^clojure.lang.IMapIterable m))
                       (iterator-seq (.valIterator ^clojure.lang.IMapIterable m))])]
      (doseq [m ms
              hh [h g]
              v (let [v (proof/seal hh m)]
                  [v (assoc v :a 9) (assoc v (or (first ks) :a) 9) (dissoc v :a) (dissoc v :x) (assoc v :y 1) (merge v {:b 1 :x nil})
                   (persistent! (-> (transient v) (assoc! :q 1) (dissoc! :a)))])
              :let [p (into {} (seq v))]]
        (is (= (count p) (count v)) "count")
        (is (= [(seq v) (keys v) (vals v)] (map seq (its v))) "the iterators walk the seq's entries, keys and values, in its order")
        (is (= (set (keys p)) (set (keys v))))))))

(deftest a-definition-declares-at-most-250-keys
  (let [ks (fn [n] (mapv #(keyword "w" (str "k" %)) (range n)))]
    (is (= :too-many-keys (:kind (proof/refusal key-class/strategy {:keys (ks 251)}))))
    (is (some? (refusal {:keys (ks 251)})) "define-type refuses what refusal answers")
    (let [log (atom [])
          h   (change-guarded (ks 250) log)
          m   (assoc (zipmap (ks 250) (range)) :x 1)
          v   (proof/seal h m)
          k   :w/k249]
      (is (= m v))
      (is (= 251 (count v)))
      (doseq [[f g] [[#(assoc % k :n) #(assoc % k :n)] [#(assoc % :a 2) #(assoc % :a 2)] [#(dissoc % k) #(dissoc % k)]
                     [#(merge % {k 0 :w/k0 nil}) #(merge % {k 0 :w/k0 nil})] [#(into % {:x 2 k 3}) #(into % {:x 2 k 3})]]]
        (let [r (f v)]
          (is (proof/proven? h r))
          (is (= (g m) r))
          (is (= (count (g m)) (count r)))))
      (is (= (set (keys m)) (set (keys v)))))))

(def ^:private jit-limit
  "HotSpot compiles no method of more bytecode than this (DontCompileHugeMethods)."
  8000)

(deftest every-method-of-a-type-is-small-enough-to-compile
  ;; the widths of the cost bench and past them; methods past jit-limit would run interpreted
  (if-let [cf (try (Class/forName "java.lang.classfile.ClassFile") (catch ClassNotFoundException _ nil))]
    (doseq [n [1 4 12 30 35 64 128 160]]
      (let [bytes ((var-get #'key-class/value-class-bytes) "x/T" [] [] (mapv #(keyword (str "k" %)) (range n)))
            parsed (clojure.lang.Reflector/invokeInstanceMethod
                    (clojure.lang.Reflector/invokeStaticMethod cf "of" (object-array 0)) "parse" (object-array [bytes]))]
        (doseq [m (.methods ^java.lang.classfile.ClassModel parsed)
                :let [c (.orElse (.code ^java.lang.classfile.MethodModel m) nil)]
                :when c]
          (is (<= (alength (.codeArray ^java.lang.classfile.attribute.CodeAttribute c)) jit-limit)
              (str n " keys: " (.stringValue (.methodName ^java.lang.classfile.MethodModel m)))))))
    (is true "this JDK has no java.lang.classfile to read the class with")))

(deftest the-assoc-of-a-declared-key-is-the-values-own
  (is (= :map-method (:kind (proof/refusal key-class/strategy
                                           {:keys [:a] :interfaces [recognitum.key_class_test.Assocs]
                                            :methods {'[assoc$0 1] (fn [_ _])}}))))
  (is (nil? (proof/refusal key-class/strategy {:keys [:a] :interfaces [Plain] :methods {'[show 0] (fn [_])}}))))
