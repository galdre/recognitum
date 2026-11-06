(ns recognitum.proof.key-class
  "The key-class proof strategy: each definition of a type emits a final APersistentMap
  subclass T whose one public constructor needs T's key, and a draft class T$Draft whose
  mark needs it too. The handle `define-type` returns holds the key; this namespace holds
  none, so reloading it loses nothing and strands nothing.

    T  extends APersistentMap implements IObj, IEditableCollection, IMapIterable,
       recognitum.proof.Proven and each interface its definition lists; where the definition declares keys, also
       IKeywordLookup. final. Holds one field f<i> per declared key K<i>, ABSENT where the
       value lacks that key, a private map `ext` of its other entries, a private `_meta`
       and a private count `cnt`, which every constructor sets. T(Object key, Object data) throws unless key is T.KEY, splits data into the
       fields and ext, and takes data's meta. Reads of a declared key read its field, others
       forward to ext; a keyword's lookup of a declared key reads the field through a thunk
       class T$K<i>, as on a defrecord. seq conses the present fields' entries, in the order
       of the keys, onto ext's seq; iterator, keyIterator and valIterator are a T$I, which
       walks the same entries reading the fields; equiv and equals against
       another T compare field by field, then ext. Private static volatiles WRITES, GATE, CHG
       and, per declared key, G<i> are set once, with the key, by install(key, writes, gate,
       guards, changes): while
       WRITES is set, assoc and without return WRITES.invoke(this, entries, k, v), v the
       strategy's marker for a removed key on without, and assocEx and cons return
       WRITES.invoke(this, entries), entries the whole new map, each one checked write that
       seals or throws; asTransient returns WRITES.invoke(this), a transient whose
       persistent! makes one checked write (into). Where G<i> is set, an assoc of K<i> to a
       v not identical to f<i> calls G<i>.invoke(this, v) in place of WRITES, and where that
       returns, returns a T made by a private constructor from this with f<i> set to v; the
       guard is handed no way to make a value. Where CHG is set, every other assoc, and
       without and cons, call CHG.invoke(this, ...) in place of WRITES: it answers the net
       change as flat pairs after the change guard returned, or null where nothing changes,
       and the change returns a T made by a private constructor from this and those pairs,
       or this. asTransient then returns CHG.invoke(this), a transient whose persistent! is
       one cons of what it was told. CHG holds no key. While WRITES is not set, every other change
       returns a plain map. A public static gate() returns
       GATE, which needs no key to call and has no four-argument arity. A no-op assoc,
       without or cons returns this. empty throws, as on a defrecord. withMeta with the same
       meta returns this. writeReplace serializes a plain map; readObject throws. A static
       create(IPersistentMap) returns its argument, so #T{...} reads back as a plain map.
       Each method the definition gives a function, `toString` included, and each
       abstract method of a listed interface that T does not already have, is a
       forwarding method: it calls the function in a private static FNS table, set once by
       claim(fns, removed) when the type is defined, with the value itself and the call's arguments,
       boxed; a slot with no function throws UnsupportedOperationException. The function
       sees no key. A default method with no function keeps its body; two default bodies
       of one method, from interfaces neither of which extends the other, and no function,
       refuse the definition.
    T$Draft implements BiConsumer (accept(key, check): mark) and Predicate (test(check):
       passed?), and none of the listed interfaces: a definition may not list either, nor an
       interface they extend. accept throws unless key is T.KEY. A
       public static gate() returns T.gate(). `define` records on the class, through a
       ClassValue, that it made it, so the keyless `marked?` answers test(check) of its own
       drafts and false of any other object, whatever its class is named.

  T$New is an AFn whose invoke(key, data) returns new T(key, data), for the handle's seal; it
  holds no key. T$I's constructor is package-private: only T makes one.

  An assoc of declared key K<i> is a private method assoc$i of its own, which the JIT inlines
  into the call site's assoc; where its guard returns it calls a private constructor taking
  every field, as a defrecord's assoc does. A definition declares at most 250 keys.

  T.KEY is a package-private static made in <clinit>. claim(fns, removed) hands it out
  once, to `define-type`. Besides recognitum.proof.Proven, defined by a namespace that is never
  reloaded, and the interfaces a definition lists, only JDK and clojure.lang interfaces
  appear in the classes.

  A value prints as its map, so the text shows its data alone, and reads back as a plain
  map; under *print-dup* it prints as T/create of its map, which reads back plain too. Where
  a listed interface or a supertype of it has a `print-method` or `print-dup` entry, the
  definition prefers the map's entry to it, and is refused, with nothing changed, where
  that entry is already preferred to the map's.

  `refusal` and `define-type` refuse through one analysis of the definition: `define-type`
  throws, as `ex-info` data, exactly the refusal `refusal` answers. The kinds beyond the
  protocol's: `:malformed` (the shape of the definition, its keys or a signature),
  `:too-many-keys` (more than 250 declared keys), `:not-a-function`,
  `:duplicate` (two signatures of one method), `:not-an-interface`, `:draft-interface`
  (an interface a draft implements) and `:reloaded-interface` (a listed interface whose name
  now loads another class)."
  (:require [clojure.string :as str]
            [recognitum.proof :as proof])
  (:import [clojure.asm ClassWriter Opcodes Type Label MethodVisitor]
           [clojure.lang DynamicClassLoader MultiFn RT]
           [java.lang.reflect Method Modifier]))

(set! *warn-on-reflection* true)

(def ^:private OBJ "java/lang/Object")
(def ^:private OBJ-D "Ljava/lang/Object;")
(def ^:private IPM "clojure/lang/IPersistentMap")
(def ^:private IPM-D "Lclojure/lang/IPersistentMap;")
(def ^:private IFN "clojure/lang/IFn")
(def ^:private IFN-D "Lclojure/lang/IFn;")

(defn- iname [^Class c] (Type/getInternalName c))
(defn- mdesc [^Class c ^String n & ps] (Type/getMethodDescriptor (.getMethod c n (into-array Class ps))))

(defn- throw! [^MethodVisitor mv ^Class ex ^String msg]
  (.visitTypeInsn mv Opcodes/NEW (iname ex))
  (.visitInsn mv Opcodes/DUP)
  (.visitLdcInsn mv msg)
  (.visitMethodInsn mv Opcodes/INVOKESPECIAL (iname ex) "<init>" "(Ljava/lang/String;)V" false)
  (.visitInsn mv Opcodes/ATHROW))

(defn- require-key!
  "if (local[slot] != T.KEY) throw new SecurityException(msg)"
  [^MethodVisitor mv t slot msg]
  (let [ok (Label.)]
    (.visitVarInsn mv Opcodes/ALOAD (int slot))
    (.visitFieldInsn mv Opcodes/GETSTATIC t "KEY" OBJ-D)
    (.visitJumpInsn mv Opcodes/IF_ACMPEQ ok)
    (throw! mv SecurityException msg)
    (.visitLabel mv ok)))

(defn- method ^MethodVisitor [^ClassWriter cw access n desc]
  (doto (.visitMethod cw (int access) n desc nil nil) (.visitCode)))

(defn- end! [^MethodVisitor mv] (.visitMaxs mv 0 0) (.visitEnd mv))

(defn- op! [^MethodVisitor mv & ops] (doseq [o ops] (.visitInsn mv (int o))))
(defn- aload! [^MethodVisitor mv slot] (.visitVarInsn mv Opcodes/ALOAD (int slot)))
(defn- astore! [^MethodVisitor mv slot] (.visitVarInsn mv Opcodes/ASTORE (int slot)))
(defn- jump! [^MethodVisitor mv opcode ^Label l] (.visitJumpInsn mv (int opcode) l))
(defn- static! [^MethodVisitor mv t n d] (.visitFieldInsn mv Opcodes/GETSTATIC t n d))
(defn- invoke! [^MethodVisitor mv ^Class owner n & ps]
  (.visitMethodInsn mv Opcodes/INVOKEINTERFACE (iname owner) n (apply mdesc owner n ps) true))
(defn- cast! [^MethodVisitor mv ^Class c] (.visitTypeInsn mv Opcodes/CHECKCAST (iname c)))

(defn- load-ext
  "this.ext: the entries under keys the definition does not declare."
  [^MethodVisitor mv t]
  (aload! mv 0)
  (.visitFieldInsn mv Opcodes/GETFIELD t "ext" IPM-D))

(defn- load-field
  "this.f<i>: the field of the i-th declared key, ABSENT where the value lacks that key."
  [^MethodVisitor mv t i]
  (aload! mv 0)
  (.visitFieldInsn mv Opcodes/GETFIELD t (str "f" i) OBJ-D))

(defn- load-key [mv t i] (static! mv t (str "K" i) OBJ-D))
(defn- load-absent [mv t] (static! mv t "ABSENT" OBJ-D))

(defn- unless-absent!
  "if (this.f<i> != ABSENT) { (body) }"
  [^MethodVisitor mv t i body]
  (let [skip (Label.)]
    (load-field mv t i)
    (load-absent mv t)
    (jump! mv Opcodes/IF_ACMPEQ skip)
    (body)
    (.visitLabel mv skip)))

(defn- by-key!
  "For each declared key i of `ks`: if (local[slot] == K<i>) { (body i) }, each body ending in
  a return or a jump; after them, the code for a key not declared. Keywords are interned, so
  identity is their equality. Past eight keys, a switch on the keyword's hash picks the keys
  to compare, as `case` does for a defrecord, so a late key costs no more than an early one."
  [^MethodVisitor mv t ks slot body]
  (let [n (count ks)
        test! (fn [i]
                (let [next (Label.)]
                  (aload! mv slot)
                  (load-key mv t i)
                  (jump! mv Opcodes/IF_ACMPNE next)
                  (body i)
                  (.visitLabel mv next)))]
    (if (<= n 8)
      (dotimes [i n] (test! i))
      (let [groups (into (sorted-map) (group-by #(.hasheq ^clojure.lang.Keyword (nth ks %)) (range n)))
            labels (vec (repeatedly (count groups) #(Label.)))
            done (Label.)]
        (aload! mv slot)
        (.visitTypeInsn mv Opcodes/INSTANCEOF "clojure/lang/Keyword")
        (jump! mv Opcodes/IFEQ done)
        (aload! mv slot)
        (.visitTypeInsn mv Opcodes/CHECKCAST "clojure/lang/Keyword")
        (.visitMethodInsn mv Opcodes/INVOKEVIRTUAL "clojure/lang/Keyword" "hasheq" "()I" false)
        (.visitLookupSwitchInsn mv done (int-array (keys groups)) (into-array Label labels))
        (doseq [[l is] (map vector labels (vals groups))]
          (.visitLabel mv l)
          (doseq [i is] (test! i))
          (jump! mv Opcodes/GOTO done))
        (.visitLabel mv done)))))

(defn- load-entries
  "withExt(this.ext): the value's entries as a plain map."
  [^MethodVisitor mv t]
  (aload! mv 0)
  (load-ext mv t)
  (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "withExt" (str "(" IPM-D ")" IPM-D) false))

(defn- write!
  "w = WRITES; if (w != null) return (IPersistentMap) w.invoke(this, local[e], more...);
   return (IPersistentMap) plain(local[e]);
  `more!` pushes the further arguments and returns how many it pushed."
  [^MethodVisitor mv t e w more!]
  (let [unhooked (Label.)]
    (static! mv t "WRITES" IFN-D)
    (astore! mv w)
    (aload! mv w)
    (jump! mv Opcodes/IFNULL unhooked)
    (aload! mv w)
    (aload! mv 0)
    (aload! mv e)
    (let [k (more!)]
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke"
                        (str "(" (apply str (repeat (+ 2 k) OBJ-D)) ")" OBJ-D) true))
    (cast! mv clojure.lang.IPersistentMap)
    (op! mv Opcodes/ARETURN)
    (.visitLabel mv unhooked)
    (aload! mv 0)
    (aload! mv e)
    (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "plain" (str "(" OBJ-D ")" OBJ-D) false)
    (cast! mv clojure.lang.IPersistentMap)
    (op! mv Opcodes/ARETURN)))

(defn- change!
  "c = CHG; if (c != null) { r = c.invoke(this, args...); if (r == null) return this;
   return new T(this, (Object[]) r); }
  `args!` pushes the arguments and returns how many it pushed. Locals `c` and `r` are scratch."
  [^MethodVisitor mv t c r args!]
  (let [unchanged (Label.) same (Label.)]
    (static! mv t "CHG" IFN-D) (astore! mv c)
    (aload! mv c) (jump! mv Opcodes/IFNULL unchanged)
    (aload! mv c) (aload! mv 0)
    (let [k (args!)]
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke"
                        (str "(" (apply str (repeat (inc k) OBJ-D)) ")" OBJ-D) true))
    (astore! mv r)
    (aload! mv r) (jump! mv Opcodes/IFNULL same)
    (.visitTypeInsn mv Opcodes/NEW t) (op! mv Opcodes/DUP)
    (aload! mv 0) (aload! mv r) (.visitTypeInsn mv Opcodes/CHECKCAST "[Ljava/lang/Object;")
    (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "<init>" (str "(L" t ";[" OBJ-D ")V") false)
    (op! mv Opcodes/ARETURN)
    (.visitLabel mv same)
    (aload! mv 0) (op! mv Opcodes/ARETURN)
    (.visitLabel mv unchanged)))

(defn- return-this-if-same!
  "if (local[a] == local[b]) return this;"
  [^MethodVisitor mv a b]
  (let [differ (Label.)]
    (aload! mv a)
    (aload! mv b)
    (jump! mv Opcodes/IF_ACMPNE differ)
    (aload! mv 0)
    (op! mv Opcodes/ARETURN)
    (.visitLabel mv differ)))

(defn- no-key-message
  "What T's constructor says when called without the key: the type, by its class name, and
  that a value is made only through the engine."
  [t]
  (str (.replace ^String t \/ \.) "'s constructor takes a key only recognitum holds: a value of this type is made only through recognitum"))

(defn- push-int! [^MethodVisitor mv n]
  (if (<= -128 n 127)
    (.visitIntInsn mv Opcodes/BIPUSH (int n))
    (.visitLdcInsn mv (int n))))

(defn- unbox-desc
  "The descriptor of the static method of RT named `n` taking `c`."
  [^String n ^Class c]
  (Type/getMethodDescriptor (.getMethod RT n (into-array Class [c]))))

(def ^:private casts
  {Integer/TYPE "intCast" Long/TYPE "longCast" Double/TYPE "doubleCast" Float/TYPE "floatCast"
   Short/TYPE "shortCast" Byte/TYPE "byteCast" Character/TYPE "charCast" Boolean/TYPE "booleanCast"})

(defn- forwarder!
  "public R name(P...) {
     f = (IFn) FNS[idx]; if (f == null) throw new UnsupportedOperationException();
     return (R) f.invoke(this, box(p)...); }
  With more than 19 parameters, f.applyTo(ArraySeq.create(this, p...))."
  [^ClassWriter cw t idx {:keys [^String name params ^Class ret]}]
  (let [ptypes (map #(Type/getType ^Class %) params)
        desc   (Type/getMethodDescriptor (Type/getType ret) (into-array Type ptypes))
        mv     (method cw Opcodes/ACC_PUBLIC name desc)
        starts (vec (reductions + 1 (map #(.getSize ^Type %) ptypes)))
        f      (int (peek starts))
        n      (count params)
        ok     (Label.)
        arg!   (fn [i]
                 (let [^Class c (nth params i) ^Type ty (nth ptypes i)]
                   (.visitVarInsn mv (.getOpcode ty Opcodes/ILOAD) (int (nth starts i)))
                   (when (.isPrimitive c)
                     (.visitMethodInsn mv Opcodes/INVOKESTATIC (iname RT) "box"
                                       (Type/getMethodDescriptor (.getMethod RT "box" (into-array Class [c]))) false))))]
    (.visitFieldInsn mv Opcodes/GETSTATIC t "FNS" "[Ljava/lang/Object;")
    (push-int! mv idx)
    (.visitInsn mv Opcodes/AALOAD)
    (.visitVarInsn mv Opcodes/ASTORE f)
    (.visitVarInsn mv Opcodes/ALOAD f)
    (.visitJumpInsn mv Opcodes/IFNONNULL ok)
    (throw! mv UnsupportedOperationException (str "no function implements " name))
    (.visitLabel mv ok)
    (.visitVarInsn mv Opcodes/ALOAD f)
    (.visitTypeInsn mv Opcodes/CHECKCAST IFN)
    (if (< n 20)
      (do (.visitVarInsn mv Opcodes/ALOAD 0)
          (dotimes [i n] (arg! i))
          (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke"
                            (str "(" (apply str (repeat (inc n) OBJ-D)) ")" OBJ-D) true))
      (do (push-int! mv (inc n))
          (.visitTypeInsn mv Opcodes/ANEWARRAY OBJ)
          (.visitInsn mv Opcodes/DUP) (push-int! mv 0) (.visitVarInsn mv Opcodes/ALOAD 0) (.visitInsn mv Opcodes/AASTORE)
          (dotimes [i n]
            (.visitInsn mv Opcodes/DUP) (push-int! mv (inc i)) (arg! i) (.visitInsn mv Opcodes/AASTORE))
          (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/ArraySeq" "create"
                            "([Ljava/lang/Object;)Lclojure/lang/ArraySeq;" false)
          (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "applyTo" "(Lclojure/lang/ISeq;)Ljava/lang/Object;" true)))
    (cond
      (= ret Void/TYPE) (do (.visitInsn mv Opcodes/POP) (.visitInsn mv Opcodes/RETURN))
      (.isPrimitive ret) (do (.visitMethodInsn mv Opcodes/INVOKESTATIC (iname RT) (casts ret) (unbox-desc (casts ret) Object) false)
                             (.visitInsn mv (.getOpcode (Type/getType ret) Opcodes/IRETURN)))
      :else (do (when-not (= ret Object) (.visitTypeInsn mv Opcodes/CHECKCAST (iname ret)))
                (.visitInsn mv Opcodes/ARETURN)))
    (end! mv)))

(defn- maker-bytes
  "T$New's bytes: an AFn whose invoke(key, data) returns new T(key, data), so the handle calls
  T's constructor without reflection. It holds no key: T's constructor still checks the one it
  is given."
  [t]
  (let [cw (ClassWriter. ClassWriter/COMPUTE_FRAMES)
        afn (iname clojure.lang.AFn)]
    (.visit cw Opcodes/V1_8 (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_SUPER) (str t "$New") nil afn
            (make-array String 0))
    (doto (method cw Opcodes/ACC_PUBLIC "<init>" "()V")
      (aload! 0)
      (.visitMethodInsn Opcodes/INVOKESPECIAL afn "<init>" "()V" false)
      (op! Opcodes/RETURN) (end!))
    (doto (method cw Opcodes/ACC_PUBLIC "invoke" (str "(" OBJ-D OBJ-D ")" OBJ-D))
      (.visitTypeInsn Opcodes/NEW t)
      (op! Opcodes/DUP)
      (aload! 1)
      (aload! 2)
      (.visitMethodInsn Opcodes/INVOKESPECIAL t "<init>" (str "(" OBJ-D OBJ-D ")V") false)
      (op! Opcodes/ARETURN)
      (end!))
    (.visitEnd cw)
    (.toByteArray cw)))

(defn- thunk-name
  "The internal name of the lookup thunk of the i-th declared key of T, `t`."
  [t i]
  (str t "$K" i))

(defn- thunk-bytes
  "T$K<i>'s bytes: an ILookupThunk whose get(target) reads field f<i> of a T, absent as
  null, and answers itself for any other target, so the keyword's call site looks again."
  [t i]
  (let [cw (ClassWriter. ClassWriter/COMPUTE_FRAMES)
        k  (thunk-name t i)]
    (.visit cw Opcodes/V1_8 (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_SUPER) k nil OBJ
            (into-array String [(iname clojure.lang.ILookupThunk)]))
    (doto (method cw Opcodes/ACC_PUBLIC "<init>" "()V")
      (aload! 0)
      (.visitMethodInsn Opcodes/INVOKESPECIAL OBJ "<init>" "()V" false)
      (op! Opcodes/RETURN) (end!))
    (let [mv (method cw Opcodes/ACC_PUBLIC "get" (mdesc clojure.lang.ILookupThunk "get" Object))
          other (Label.) absent (Label.)]
      (aload! mv 1)
      (jump! mv Opcodes/IFNULL other)
      (aload! mv 1)
      (.visitMethodInsn mv Opcodes/INVOKEVIRTUAL OBJ "getClass" "()Ljava/lang/Class;" false)
      (.visitLdcInsn mv (Type/getObjectType t))
      (jump! mv Opcodes/IF_ACMPNE other)
      (aload! mv 1)
      (.visitTypeInsn mv Opcodes/CHECKCAST t)
      (.visitFieldInsn mv Opcodes/GETFIELD t (str "f" i) OBJ-D)
      (astore! mv 2)
      (aload! mv 2)
      (static! mv t "ABSENT" OBJ-D)
      (jump! mv Opcodes/IF_ACMPEQ absent)
      (aload! mv 2)
      (op! mv Opcodes/ARETURN)
      (.visitLabel mv absent)
      (op! mv Opcodes/ACONST_NULL Opcodes/ARETURN)
      (.visitLabel mv other)
      (aload! mv 0)
      (op! mv Opcodes/ARETURN)
      (end! mv))
    (.visitEnd cw)
    (.toByteArray cw)))

(def ^:private max-keys
  "The most keys a definition declares: T has a constructor taking every field, which the
  assoc of each key calls with the fields pushed in order, and a constructor takes at most
  255 slots, this and meta, ext and the count among them. A defrecord's constructor has the
  same bound."
  250)

(defn- flat-desc
  "The descriptor of T's constructor taking meta, ext, the count and the n fields."
  [n]
  (str "(" IPM-D IPM-D "I" (apply str (repeat n OBJ-D)) ")V"))

(defn- iter-name
  "The internal name of the iterator class of T, `t`."
  [t]
  (str t "$I"))

(defn- iter-bytes
  "T$I's bytes: an Iterator over a T's present fields, in the order of the keys, then over
  its ext, answering entries (mode 0), keys (1) or values (2). It reads the fields of the T
  it is given, so no seq or map is built; its keys are its own K<i>."
  [t ks]
  (let [cw   (ClassWriter. ClassWriter/COMPUTE_FRAMES)
        c    (iter-name t)
        n    (count ks)
        T-D  (str "L" t ";")
        IT-D "Ljava/util/Iterator;"
        pub  Opcodes/ACC_PUBLIC
        priv Opcodes/ACC_PRIVATE
        fin  Opcodes/ACC_FINAL
        fld  (fn [^MethodVisitor mv nm d] (aload! mv 0) (.visitFieldInsn mv Opcodes/GETFIELD c nm d))
        ;; tableswitch on the int in local `slot` over the n fields, (body j) for each, each
        ;; ending in a return or a jump; falls through for an index past them
        switch! (fn [^MethodVisitor mv slot body]
                  (when (pos? n)
                    (let [labels (vec (repeatedly n #(Label.))) dflt (Label.)]
                      (.visitVarInsn mv Opcodes/ILOAD (int slot))
                      (.visitTableSwitchInsn mv 0 (dec n) dflt (into-array Label labels))
                      (doseq [j (range n)] (.visitLabel mv (labels j)) (body j))
                      (.visitLabel mv dflt))))
        field! (fn [^MethodVisitor mv j]
                 (fld mv "t" T-D) (.visitFieldInsn mv Opcodes/GETFIELD t (str "f" j) OBJ-D))]
    (.visit cw Opcodes/V1_8 (bit-or pub fin Opcodes/ACC_SUPER) c nil OBJ (into-array String ["java/util/Iterator"]))
    (doseq [[acc nm d] (concat [[(bit-or priv fin) "t" T-D] [(bit-or priv fin) "ext" IPM-D] [(bit-or priv fin) "mode" "I"]
                                [priv "i" "I"] [priv "it" IT-D]]
                               (for [j (range n)] [(bit-or priv Opcodes/ACC_STATIC fin) (str "K" j) OBJ-D]))]
      (.visitEnd (.visitField cw (int acc) nm d nil nil)))
    (let [mv (method cw Opcodes/ACC_STATIC "<clinit>" "()V")]
      (doseq [[j k] (map-indexed vector ks)]
        (if-let [kns (namespace k)] (.visitLdcInsn mv kns) (op! mv Opcodes/ACONST_NULL))
        (.visitLdcInsn mv (name k))
        (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/Keyword" "intern"
                          "(Ljava/lang/String;Ljava/lang/String;)Lclojure/lang/Keyword;" false)
        (.visitFieldInsn mv Opcodes/PUTSTATIC c (str "K" j) OBJ-D))
      (op! mv Opcodes/RETURN) (end! mv))
    ;; T$I(T t, IPersistentMap ext, int mode), package-private: T makes it
    (doto (method cw 0 "<init>" (str "(" T-D IPM-D "I)V"))
      (aload! 0) (.visitMethodInsn Opcodes/INVOKESPECIAL OBJ "<init>" "()V" false)
      (aload! 0) (aload! 1) (.visitFieldInsn Opcodes/PUTFIELD c "t" T-D)
      (aload! 0) (aload! 2) (.visitFieldInsn Opcodes/PUTFIELD c "ext" IPM-D)
      (aload! 0) (.visitVarInsn Opcodes/ILOAD 3) (.visitFieldInsn Opcodes/PUTFIELD c "mode" "I")
      (op! Opcodes/RETURN) (end!))
    ;; private boolean field(): skips absent fields; whether i is a present field
    (let [mv (method cw priv "field" "()Z")
          top (Label.) skip (Label.)]
      (.visitLabel mv top)
      (fld mv "i" "I") (.visitVarInsn mv Opcodes/ISTORE 1)
      (switch! mv 1 (fn [j]
                      (field! mv j) (static! mv t "ABSENT" OBJ-D)
                      (jump! mv Opcodes/IF_ACMPEQ skip)
                      (op! mv Opcodes/ICONST_1 Opcodes/IRETURN)))
      (op! mv Opcodes/ICONST_0 Opcodes/IRETURN)
      (.visitLabel mv skip)
      (aload! mv 0) (.visitVarInsn mv Opcodes/ILOAD 1) (op! mv Opcodes/ICONST_1 Opcodes/IADD)
      (.visitFieldInsn mv Opcodes/PUTFIELD c "i" "I")
      (jump! mv Opcodes/GOTO top)
      (end! mv))
    ;; private Iterator rest(): ext's iterator, made once
    (let [mv (method cw priv "rest" (str "()" IT-D)) made (Label.)]
      (fld mv "it" IT-D) (jump! mv Opcodes/IFNONNULL made)
      (aload! mv 0) (fld mv "ext" IPM-D) (invoke! mv Iterable "iterator")
      (.visitFieldInsn mv Opcodes/PUTFIELD c "it" IT-D)
      (.visitLabel mv made)
      (fld mv "it" IT-D) (op! mv Opcodes/ARETURN) (end! mv))
    (let [mv (method cw pub "hasNext" "()Z") rest (Label.)]
      (aload! mv 0) (.visitMethodInsn mv Opcodes/INVOKESPECIAL c "field" "()Z" false)
      (jump! mv Opcodes/IFEQ rest)
      (op! mv Opcodes/ICONST_1 Opcodes/IRETURN)
      (.visitLabel mv rest)
      (aload! mv 0) (.visitMethodInsn mv Opcodes/INVOKESPECIAL c "rest" (str "()" IT-D) false)
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Iterator" "hasNext" "()Z" true)
      (op! mv Opcodes/IRETURN) (end! mv))
    ;; public Object next(): the field at i, as the mode asks, and i moves on; else ext's next
    (let [mv (method cw pub "next" (str "()" OBJ-D)) rest (Label.) entry (Label.) key (Label.)]
      (aload! mv 0) (.visitMethodInsn mv Opcodes/INVOKESPECIAL c "field" "()Z" false)
      (jump! mv Opcodes/IFEQ rest)
      (fld mv "i" "I") (.visitVarInsn mv Opcodes/ISTORE 1)
      (aload! mv 0) (.visitVarInsn mv Opcodes/ILOAD 1) (op! mv Opcodes/ICONST_1 Opcodes/IADD)
      (.visitFieldInsn mv Opcodes/PUTFIELD c "i" "I")
      (switch! mv 1 (fn [j]
                      (static! mv c (str "K" j) OBJ-D) (astore! mv 2)
                      (field! mv j) (astore! mv 3)
                      (jump! mv Opcodes/GOTO entry)))
      (.visitLabel mv rest)
      (aload! mv 0) (.visitMethodInsn mv Opcodes/INVOKESPECIAL c "rest" (str "()" IT-D) false)
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Iterator" "next" (str "()" OBJ-D) true)
      (astore! mv 4)
      (fld mv "mode" "I") (jump! mv Opcodes/IFNE key)
      (aload! mv 4) (op! mv Opcodes/ARETURN)
      (.visitLabel mv key)
      (aload! mv 4) (cast! mv java.util.Map$Entry)
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Map$Entry" "getKey" (str "()" OBJ-D) true) (astore! mv 2)
      (aload! mv 4) (cast! mv java.util.Map$Entry)
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Map$Entry" "getValue" (str "()" OBJ-D) true) (astore! mv 3)
      (.visitLabel mv entry)
      (let [not-entry (Label.) not-key (Label.)]
        (fld mv "mode" "I") (jump! mv Opcodes/IFNE not-entry)
        (aload! mv 2) (aload! mv 3)
        (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/MapEntry" "create"
                          (str "(" OBJ-D OBJ-D ")Lclojure/lang/MapEntry;") false)
        (op! mv Opcodes/ARETURN)
        (.visitLabel mv not-entry)
        (fld mv "mode" "I") (op! mv Opcodes/ICONST_1) (jump! mv Opcodes/IF_ICMPNE not-key)
        (aload! mv 2) (op! mv Opcodes/ARETURN)
        (.visitLabel mv not-key)
        (aload! mv 3) (op! mv Opcodes/ARETURN))
      (end! mv))
    (.visitEnd cw)
    (.toByteArray cw)))

(defn- walk-methods!
  "T's seq and iterators: seq conses the present fields' entries, in the order of the keys,
  onto ext's seq, so no map is built; iterator, keyIterator and valIterator are a T$I, which
  walks the same entries reading the fields."
  [^ClassWriter cw t n]
  (let [pub Opcodes/ACC_PUBLIC ret Opcodes/ARETURN]
    (let [mv (method cw pub "seq" (mdesc clojure.lang.Seqable "seq"))]
      (load-ext mv t) (invoke! mv clojure.lang.Seqable "seq") (astore! mv 1)
      (doseq [i (range (dec n) -1 -1)]
        (unless-absent! mv t i
                        (fn []
                          (.visitTypeInsn mv Opcodes/NEW "clojure/lang/Cons") (op! mv Opcodes/DUP)
                          (load-key mv t i) (load-field mv t i)
                          (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/MapEntry" "create"
                                            (str "(" OBJ-D OBJ-D ")Lclojure/lang/MapEntry;") false)
                          (aload! mv 1)
                          (.visitMethodInsn mv Opcodes/INVOKESPECIAL "clojure/lang/Cons" "<init>"
                                            (str "(" OBJ-D "Lclojure/lang/ISeq;)V") false)
                          (astore! mv 1))))
      (aload! mv 1) (op! mv ret) (end! mv))
    ;; iterator, keyIterator and valIterator: a T$I over the fields and ext
    (doseq [[nm mode] [["iterator" 0] ["keyIterator" 1] ["valIterator" 2]]]
      (doto (method cw pub nm "()Ljava/util/Iterator;")
        (.visitTypeInsn Opcodes/NEW (iter-name t)) (op! Opcodes/DUP)
        (aload! 0) (load-ext t) (.visitInsn (int (+ Opcodes/ICONST_0 mode)))
        (.visitMethodInsn Opcodes/INVOKESPECIAL (iter-name t) "<init>" (str "(L" t ";" IPM-D "I)V") false)
        (op! ret) (end!)))))

(defn- folds-of
  "The [method interface] pairs of reduce and kvreduce that T implements itself: each, unless
  a method of the plan has its name and parameters."
  [plan]
  (let [listed? (fn [nm] (some #(and (= nm (:name %)) (= [clojure.lang.IFn Object] (vec (:params %)))) plan))]
    (remove (comp listed? first) [["reduce" clojure.lang.IReduceInit] ["kvreduce" clojure.lang.IKVReduce]])))

(defn- fold-methods!
  "reduce(f, init) calls f with each entry, kvreduce(f, init) with each key and value: the
  present fields in the order of the keys, then ext's entries, stopping at a reduced."
  [^ClassWriter cw t n folds]
  (let [pub Opcodes/ACC_PUBLIC ret Opcodes/ARETURN]
    (doseq [[nm _] folds]
      (let [mv (method cw pub nm (str "(" IFN-D OBJ-D ")" OBJ-D))
            kv? (= nm "kvreduce")
            step! (fn [push!]
                    (let [go-on (Label.)]
                      (aload! mv 1) (aload! mv 2) (push!)
                      (if kv?
                        (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke" (str "(" OBJ-D OBJ-D OBJ-D ")" OBJ-D) true)
                        (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke" (str "(" OBJ-D OBJ-D ")" OBJ-D) true))
                      (astore! mv 2)
                      (aload! mv 2)
                      (.visitMethodInsn mv Opcodes/INVOKESTATIC (iname RT) "isReduced" (str "(" OBJ-D ")Z") false)
                      (jump! mv Opcodes/IFEQ go-on)
                      (aload! mv 2) (cast! mv clojure.lang.IDeref) (invoke! mv clojure.lang.IDeref "deref") (op! mv ret)
                      (.visitLabel mv go-on)))
            top (Label.) end (Label.)]
        (dotimes [i n]
          (unless-absent! mv t i
                          #(step! (fn []
                                    (load-key mv t i) (load-field mv t i)
                                    (when-not kv?
                                      (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/MapEntry" "create"
                                                        (str "(" OBJ-D OBJ-D ")Lclojure/lang/MapEntry;") false))))))
        (load-ext mv t) (invoke! mv clojure.lang.Seqable "seq") (astore! mv 3)
        (.visitLabel mv top)
        (aload! mv 3) (jump! mv Opcodes/IFNULL end)
        (aload! mv 3) (invoke! mv clojure.lang.ISeq "first") (astore! mv 4)
        (step! (fn []
                 (aload! mv 4)
                 (when kv?
                   (cast! mv java.util.Map$Entry)
                   (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Map$Entry" "getKey" (str "()" OBJ-D) true)
                   (aload! mv 4) (cast! mv java.util.Map$Entry)
                   (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Map$Entry" "getValue" (str "()" OBJ-D) true))))
        (aload! mv 3) (invoke! mv clojure.lang.ISeq "next") (astore! mv 3)
        (jump! mv Opcodes/GOTO top)
        (.visitLabel mv end)
        (aload! mv 2) (op! mv ret)
        (end! mv)))))

(defn- equality-methods!
  "T's equiv and equals: against a value of T, field by field and then ext, with no seq; else
  the map's own."
  [^ClassWriter cw t n]
  (let [pub Opcodes/ACC_PUBLIC super (iname clojure.lang.APersistentMap)]
    (doseq [[nm util] [["equiv" "equiv"] ["equals" "equals"]]]
      (let [mv (method cw pub nm (str "(" OBJ-D ")Z"))
            other (Label.) differ (Label.)
            same! (fn [] (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/Util" util
                                           (str "(" OBJ-D OBJ-D ")Z") false))]
        (aload! mv 1) (.visitTypeInsn mv Opcodes/INSTANCEOF t) (jump! mv Opcodes/IFEQ other)
        (aload! mv 1) (.visitTypeInsn mv Opcodes/CHECKCAST t) (astore! mv 2)
        (dotimes [i n]
          (load-field mv t i)
          (aload! mv 2) (.visitFieldInsn mv Opcodes/GETFIELD t (str "f" i) OBJ-D)
          (same!) (jump! mv Opcodes/IFEQ differ))
        (load-ext mv t)
        (aload! mv 2) (.visitFieldInsn mv Opcodes/GETFIELD t "ext" IPM-D)
        (same!) (op! mv Opcodes/IRETURN)
        (.visitLabel mv differ)
        (op! mv Opcodes/ICONST_0 Opcodes/IRETURN)
        (.visitLabel mv other)
        (aload! mv 0) (aload! mv 1)
        (.visitMethodInsn mv Opcodes/INVOKESPECIAL super nm (str "(" OBJ-D ")Z") false)
        (op! mv Opcodes/IRETURN)
        (end! mv)))))

(defn- value-class-bytes
  "T's bytes. `ifaces` are the listed interfaces T implements; `plan` the methods that
  forward, each to the function at its index in FNS; `ks` the declared keys, one field each."
  [t ifaces plan ks]
  (let [cw    (ClassWriter. ClassWriter/COMPUTE_FRAMES)
        super (iname clojure.lang.APersistentMap)
        n     (count ks)
        pub   Opcodes/ACC_PUBLIC
        priv  Opcodes/ACC_PRIVATE
        stat  Opcodes/ACC_STATIC
        fin   Opcodes/ACC_FINAL
        ret   Opcodes/ARETURN
        folds (folds-of plan)]
    (.visit cw Opcodes/V1_8 (bit-or pub fin Opcodes/ACC_SUPER) t nil super
            (into-array String (concat [(iname clojure.lang.IObj) (iname clojure.lang.IEditableCollection)
                                        (iname clojure.lang.IMapIterable)
                                        (iname recognitum.proof.Proven)]
                                       (when (pos? n) [(iname clojure.lang.IKeywordLookup)])
                                       (map (comp iname second) folds)
                                       (map iname ifaces))))
    (doseq [[acc nm d] (concat [[(bit-or stat fin) "KEY" OBJ-D]
                                [(bit-or stat fin) "ABSENT" OBJ-D]
                                [(bit-or priv stat) "claimed" "Z"]
                                [(bit-or priv stat Opcodes/ACC_VOLATILE) "WRITES" IFN-D]
                                [(bit-or priv stat Opcodes/ACC_VOLATILE) "CHG" IFN-D]
                                [(bit-or priv stat Opcodes/ACC_VOLATILE) "GATE" IFN-D]
                                [(bit-or priv stat Opcodes/ACC_VOLATILE) "FNS" "[Ljava/lang/Object;"]
                                [(bit-or priv stat Opcodes/ACC_VOLATILE) "REMOVED" OBJ-D]
                                [(bit-or priv fin) "ext" IPM-D]
                                [(bit-or priv fin) "_meta" IPM-D]
                                [(bit-or priv fin) "cnt" "I"]]
                               (for [i (range n)] [(bit-or priv stat fin) (str "K" i) OBJ-D])
                               (for [i (range n)] [(bit-or priv stat Opcodes/ACC_VOLATILE) (str "G" i) IFN-D])
                               (for [i (range n)] [fin (str "f" i) OBJ-D]))]
      (.visitEnd (.visitField cw (int acc) nm d nil nil)))
    ;; static { KEY = new Object(); ABSENT = new Object(); K<i> = Keyword.intern(ns, name); }
    (let [mv (method cw stat "<clinit>" "()V")]
      (doseq [f ["KEY" "ABSENT"]]
        (.visitTypeInsn mv Opcodes/NEW OBJ)
        (op! mv Opcodes/DUP)
        (.visitMethodInsn mv Opcodes/INVOKESPECIAL OBJ "<init>" "()V" false)
        (.visitFieldInsn mv Opcodes/PUTSTATIC t f OBJ-D))
      (doseq [[i k] (map-indexed vector ks)]
        (if-let [kns (namespace k)] (.visitLdcInsn mv kns) (op! mv Opcodes/ACONST_NULL))
        (.visitLdcInsn mv (name k))
        (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/Keyword" "intern"
                          "(Ljava/lang/String;Ljava/lang/String;)Lclojure/lang/Keyword;" false)
        (.visitFieldInsn mv Opcodes/PUTSTATIC t (str "K" i) OBJ-D))
      (op! mv Opcodes/RETURN)
      (end! mv))
    ;; public static synchronized Object claim(Object[] fns, Object removed): once; sets FNS
    ;; and REMOVED, the strategy's marker for a removed key, and returns the key
    (let [mv (method cw (bit-or pub stat Opcodes/ACC_SYNCHRONIZED) "claim" (str "([Ljava/lang/Object;" OBJ-D ")" OBJ-D))
          fresh (Label.)]
      (.visitFieldInsn mv Opcodes/GETSTATIC t "claimed" "Z")
      (jump! mv Opcodes/IFEQ fresh)
      (throw! mv SecurityException "key already claimed")
      (.visitLabel mv fresh)
      (op! mv Opcodes/ICONST_1)
      (.visitFieldInsn mv Opcodes/PUTSTATIC t "claimed" "Z")
      (aload! mv 0)
      (.visitFieldInsn mv Opcodes/PUTSTATIC t "FNS" "[Ljava/lang/Object;")
      (aload! mv 1)
      (.visitFieldInsn mv Opcodes/PUTSTATIC t "REMOVED" OBJ-D)
      (static! mv t "KEY" OBJ-D)
      (op! mv ret)
      (end! mv))
    ;; public static synchronized void install(Object key, Object writes, Object gate,
    ;; Object[] guards, Object changes): once, with the key. WRITES is what the changes below
    ;; call; GATE is what gate() hands out; G<i>, where guards is not null, is guards[i], the
    ;; guard of the i-th declared key, or null for none; CHG, where changes is not null, is
    ;; what the changes call in place of WRITES.
    (let [mv (method cw (bit-or pub stat Opcodes/ACC_SYNCHRONIZED) "install" (str "(" OBJ-D OBJ-D OBJ-D "[" OBJ-D OBJ-D ")V"))
          fresh (Label.)
          unguarded (Label.)
          unchanged (Label.)]
      (require-key! mv t 0 "installing a write takes the type's key")
      (static! mv t "WRITES" IFN-D)
      (jump! mv Opcodes/IFNULL fresh)
      (throw! mv SecurityException "writes already installed")
      (.visitLabel mv fresh)
      (aload! mv 3)
      (jump! mv Opcodes/IFNULL unguarded)
      (dotimes [i n]
        (aload! mv 3) (push-int! mv i) (op! mv Opcodes/AALOAD)
        (cast! mv clojure.lang.IFn)
        (.visitFieldInsn mv Opcodes/PUTSTATIC t (str "G" i) IFN-D))
      (.visitLabel mv unguarded)
      (aload! mv 4)
      (jump! mv Opcodes/IFNULL unchanged)
      (aload! mv 4)
      (cast! mv clojure.lang.IFn)
      (.visitFieldInsn mv Opcodes/PUTSTATIC t "CHG" IFN-D)
      (.visitLabel mv unchanged)
      (aload! mv 2)
      (cast! mv clojure.lang.IFn)
      (.visitFieldInsn mv Opcodes/PUTSTATIC t "GATE" IFN-D)
      (aload! mv 1)
      (cast! mv clojure.lang.IFn)
      (.visitFieldInsn mv Opcodes/PUTSTATIC t "WRITES" IFN-D)
      (op! mv Opcodes/RETURN)
      (end! mv))
    ;; public static IFn gate() { return GATE; }
    (doto (method cw (bit-or pub stat) "gate" (str "()" IFN-D))
      (static! t "GATE" IFN-D)
      (op! ret) (end!))
    ;; public T(Object key, Object data): the key is checked before super() runs. Each field
    ;; takes data's entry under its key, or ABSENT; ext takes the other entries.
    (let [mv (method cw pub "<init>" (str "(" OBJ-D OBJ-D ")V"))
          ok (Label.)]
      (require-key! mv t 1 (no-key-message t))
      (aload! mv 2)
      (.visitTypeInsn mv Opcodes/INSTANCEOF IPM)
      (jump! mv Opcodes/IFNE ok)
      (throw! mv IllegalArgumentException "data must be a persistent map")
      (.visitLabel mv ok)
      (aload! mv 0)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL super "<init>" "()V" false)
      (aload! mv 2)
      (cast! mv clojure.lang.IPersistentMap)
      (astore! mv 3)
      (dotimes [i n]
        (aload! mv 0)
        (aload! mv 3)
        (load-key mv t i)
        (load-absent mv t)
        (invoke! mv clojure.lang.ILookup "valAt" Object Object)
        (.visitFieldInsn mv Opcodes/PUTFIELD t (str "f" i) OBJ-D))
      (if (zero? n)
        (do (aload! mv 0) (aload! mv 3))
        ;; ext = data.count() == present ? {} : data without each declared key
        (let [some-other (Label.) done (Label.)]
          (op! mv Opcodes/ICONST_0)
          (.visitVarInsn mv Opcodes/ISTORE 4)
          (dotimes [i n] (unless-absent! mv t i #(.visitIincInsn mv 4 1)))
          (aload! mv 3)
          (invoke! mv clojure.lang.Counted "count")
          (.visitVarInsn mv Opcodes/ILOAD 4)
          (jump! mv Opcodes/IF_ICMPNE some-other)
          (aload! mv 0)
          (static! mv "clojure/lang/PersistentArrayMap" "EMPTY" "Lclojure/lang/PersistentArrayMap;")
          (cast! mv clojure.lang.IPersistentMap)
          (jump! mv Opcodes/GOTO done)
          (.visitLabel mv some-other)
          (aload! mv 0)
          (aload! mv 3)
          (dotimes [i n]
            (load-key mv t i)
            (invoke! mv clojure.lang.IPersistentMap "without" Object))
          (.visitLabel mv done)))
      (.visitFieldInsn mv Opcodes/PUTFIELD t "ext" IPM-D)
      (aload! mv 0) (aload! mv 3) (invoke! mv clojure.lang.Counted "count")
      (.visitFieldInsn mv Opcodes/PUTFIELD t "cnt" "I")
      ;; _meta = data instanceof IMeta ? ((IMeta) data).meta() : null
      (let [no-meta (Label.)]
        (aload! mv 2)
        (.visitTypeInsn mv Opcodes/INSTANCEOF (iname clojure.lang.IMeta))
        (jump! mv Opcodes/IFEQ no-meta)
        (aload! mv 0)
        (aload! mv 2)
        (cast! mv clojure.lang.IMeta)
        (invoke! mv clojure.lang.IMeta "meta")
        (.visitFieldInsn mv Opcodes/PUTFIELD t "_meta" IPM-D)
        (.visitLabel mv no-meta))
      (op! mv Opcodes/RETURN)
      (end! mv))
    ;; private T(T src, IPersistentMap meta): src's entries, new meta
    (let [mv (method cw priv "<init>" (str "(L" t ";" IPM-D ")V"))]
      (aload! mv 0)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL super "<init>" "()V" false)
      (doseq [[f d] (list* ["ext" IPM-D] ["cnt" "I"] (for [i (range n)] [(str "f" i) OBJ-D]))]
        (aload! mv 0)
        (aload! mv 1)
        (.visitFieldInsn mv Opcodes/GETFIELD t f d)
        (.visitFieldInsn mv Opcodes/PUTFIELD t f d))
      (aload! mv 0)
      (aload! mv 2)
      (.visitFieldInsn mv Opcodes/PUTFIELD t "_meta" IPM-D)
      (op! mv Opcodes/RETURN)
      (end! mv))
    ;; private T(IPersistentMap meta, IPersistentMap ext, int cnt, Object f0, ...): the
    ;; fields as given. Only assoc calls it, where a guard returned.
    (when (pos? n)
      (let [mv (method cw priv "<init>" (flat-desc n))]
        (aload! mv 0)
        (.visitMethodInsn mv Opcodes/INVOKESPECIAL super "<init>" "()V" false)
        (aload! mv 0) (aload! mv 1) (.visitFieldInsn mv Opcodes/PUTFIELD t "_meta" IPM-D)
        (aload! mv 0) (aload! mv 2) (.visitFieldInsn mv Opcodes/PUTFIELD t "ext" IPM-D)
        (aload! mv 0) (.visitVarInsn mv Opcodes/ILOAD 3) (.visitFieldInsn mv Opcodes/PUTFIELD t "cnt" "I")
        (dotimes [j n]
          (aload! mv 0) (aload! mv (+ 4 j)) (.visitFieldInsn mv Opcodes/PUTFIELD t (str "f" j) OBJ-D))
        (op! mv Opcodes/RETURN)
        (end! mv)))
    ;; private static int index$(Object k): the index of declared key k, else -1
    (let [mv (method cw (bit-or priv stat) "index$" (str "(" OBJ-D ")I"))]
      (by-key! mv t ks 0 (fn [i] (push-int! mv i) (op! mv Opcodes/IRETURN)))
      (op! mv Opcodes/ICONST_M1 Opcodes/IRETURN)
      (end! mv))
    ;; private static int delta$(Object was, Object now): how a field's change moves the count
    (let [mv (method cw (bit-or priv stat) "delta$" (str "(" OBJ-D OBJ-D ")I"))
          present (Label.) same (Label.)]
      (aload! mv 0) (load-absent mv t) (jump! mv Opcodes/IF_ACMPNE present)
      (aload! mv 1) (load-absent mv t) (jump! mv Opcodes/IF_ACMPEQ same)
      (op! mv Opcodes/ICONST_1 Opcodes/IRETURN)
      (.visitLabel mv present)
      (aload! mv 1) (load-absent mv t) (jump! mv Opcodes/IF_ACMPNE same)
      (op! mv Opcodes/ICONST_M1 Opcodes/IRETURN)
      (.visitLabel mv same)
      (op! mv Opcodes/ICONST_0 Opcodes/IRETURN)
      (end! mv))
    ;; private T(T src, Object[] ch): src's entries and meta with ch's pairs k, v applied in
    ;; order, v REMOVED for a removal. Only the changes call it, with the pairs CHG answered.
    (let [mv (method cw priv "<init>" (str "(L" t ";[" OBJ-D ")V"))
          top (Label.) nxt (Label.) done (Label.) put-ext (Label.)]
      (aload! mv 0)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL super "<init>" "()V" false)
      (doseq [[f d] (cons ["_meta" IPM-D] (for [i (range n)] [(str "f" i) OBJ-D]))]
        (aload! mv 0) (aload! mv 1)
        (.visitFieldInsn mv Opcodes/GETFIELD t f d)
        (.visitFieldInsn mv Opcodes/PUTFIELD t f d))
      (aload! mv 1) (.visitFieldInsn mv Opcodes/GETFIELD t "ext" IPM-D) (astore! mv 3)
      ;; local 7: the count less ext's, kept as the fields change
      (aload! mv 1) (.visitFieldInsn mv Opcodes/GETFIELD t "cnt" "I")
      (aload! mv 3) (invoke! mv clojure.lang.Counted "count") (op! mv Opcodes/ISUB)
      (.visitVarInsn mv Opcodes/ISTORE 7)
      (op! mv Opcodes/ICONST_0) (.visitVarInsn mv Opcodes/ISTORE 4)
      (.visitLabel mv top)
      (.visitVarInsn mv Opcodes/ILOAD 4) (aload! mv 2) (op! mv Opcodes/ARRAYLENGTH)
      (jump! mv Opcodes/IF_ICMPGE done)
      (aload! mv 2) (.visitVarInsn mv Opcodes/ILOAD 4) (op! mv Opcodes/AALOAD) (astore! mv 5)
      (aload! mv 2) (.visitVarInsn mv Opcodes/ILOAD 4) (op! mv Opcodes/ICONST_1 Opcodes/IADD Opcodes/AALOAD) (astore! mv 6)
      ;; j = index$(k); a declared key's field takes v, ABSENT where v is REMOVED, through a
      ;; switch on j, so each key costs a few instructions here
      (aload! mv 5)
      (.visitMethodInsn mv Opcodes/INVOKESTATIC t "index$" (str "(" OBJ-D ")I") false)
      (.visitVarInsn mv Opcodes/ISTORE 9)
      (when (pos? n)
        (let [undeclared (Label.) keep (Label.) put (Label.) labels (vec (repeatedly n #(Label.)))]
          (.visitVarInsn mv Opcodes/ILOAD 9) (jump! mv Opcodes/IFLT undeclared)
          (aload! mv 6) (static! mv t "REMOVED" OBJ-D)
          (jump! mv Opcodes/IF_ACMPNE keep)
          (load-absent mv t)
          (jump! mv Opcodes/GOTO put)
          (.visitLabel mv keep)
          (aload! mv 6)
          (.visitLabel mv put)
          (astore! mv 8)
          (.visitVarInsn mv Opcodes/ILOAD 9)
          (.visitTableSwitchInsn mv 0 (dec n) undeclared (into-array Label labels))
          (dotimes [i n]
            (.visitLabel mv (labels i))
            (load-field mv t i) (aload! mv 8)
            (.visitMethodInsn mv Opcodes/INVOKESTATIC t "delta$" (str "(" OBJ-D OBJ-D ")I") false)
            (.visitVarInsn mv Opcodes/ILOAD 7) (op! mv Opcodes/IADD) (.visitVarInsn mv Opcodes/ISTORE 7)
            (aload! mv 0) (aload! mv 8)
            (.visitFieldInsn mv Opcodes/PUTFIELD t (str "f" i) OBJ-D)
            (jump! mv Opcodes/GOTO nxt))
          (.visitLabel mv undeclared)))
      (aload! mv 6) (static! mv t "REMOVED" OBJ-D)
      (jump! mv Opcodes/IF_ACMPNE put-ext)
      (aload! mv 3) (aload! mv 5) (invoke! mv clojure.lang.IPersistentMap "without" Object) (astore! mv 3)
      (jump! mv Opcodes/GOTO nxt)
      (.visitLabel mv put-ext)
      (aload! mv 3) (aload! mv 5) (aload! mv 6) (invoke! mv clojure.lang.IPersistentMap "assoc" Object Object) (astore! mv 3)
      (.visitLabel mv nxt)
      (.visitIincInsn mv 4 2)
      (jump! mv Opcodes/GOTO top)
      (.visitLabel mv done)
      (aload! mv 0) (aload! mv 3) (.visitFieldInsn mv Opcodes/PUTFIELD t "ext" IPM-D)
      (aload! mv 0) (.visitVarInsn mv Opcodes/ILOAD 7) (aload! mv 3) (invoke! mv clojure.lang.Counted "count") (op! mv Opcodes/IADD)
      (.visitFieldInsn mv Opcodes/PUTFIELD t "cnt" "I")
      (op! mv Opcodes/RETURN)
      (end! mv))
    ;; private IPersistentMap withExt(IPersistentMap e): the present fields' entries, in the
    ;; order of the keys, then e's
    (let [mv (method cw priv "withExt" (str "(" IPM-D ")" IPM-D))]
      (if (zero? n)
        (do (aload! mv 1) (op! mv ret))
        (let [more (Label.)]
          (op! mv Opcodes/ICONST_0)
          (.visitVarInsn mv Opcodes/ISTORE 2)
          (dotimes [i n] (unless-absent! mv t i #(.visitIincInsn mv 2 1)))
          (.visitVarInsn mv Opcodes/ILOAD 2)
          (op! mv Opcodes/ICONST_1 Opcodes/ISHL)
          (.visitTypeInsn mv Opcodes/ANEWARRAY OBJ)
          (astore! mv 3)
          (op! mv Opcodes/ICONST_0)
          (.visitVarInsn mv Opcodes/ISTORE 4)
          (dotimes [i n]
            (unless-absent! mv t i
                            (fn []
                              (aload! mv 3) (.visitVarInsn mv Opcodes/ILOAD 4) (load-key mv t i) (op! mv Opcodes/AASTORE)
                              (aload! mv 3) (.visitVarInsn mv Opcodes/ILOAD 4) (op! mv Opcodes/ICONST_1 Opcodes/IADD)
                              (load-field mv t i) (op! mv Opcodes/AASTORE)
                              (.visitIincInsn mv 4 2))))
          (aload! mv 3)
          (.visitMethodInsn mv Opcodes/INVOKESTATIC (iname RT) "mapUniqueKeys" (str "([Ljava/lang/Object;)" IPM-D) false)
          (astore! mv 5)
          (aload! mv 1)
          (invoke! mv clojure.lang.Counted "count")
          (jump! mv Opcodes/IFNE more)
          (aload! mv 5)
          (op! mv ret)
          (.visitLabel mv more)
          (aload! mv 5)
          (aload! mv 1)
          (invoke! mv clojure.lang.IPersistentCollection "cons" Object)
          (cast! mv clojure.lang.IPersistentMap)
          (op! mv ret)))
      (end! mv))
    ;; private Object plain(Object r): r with this value's meta, if it has any
    (let [mv (method cw priv "plain" (str "(" OBJ-D ")" OBJ-D))
          some-meta (Label.)]
      (aload! mv 0)
      (.visitFieldInsn mv Opcodes/GETFIELD t "_meta" IPM-D)
      (jump! mv Opcodes/IFNONNULL some-meta)
      (aload! mv 1)
      (op! mv ret)
      (.visitLabel mv some-meta)
      (aload! mv 1)
      (cast! mv clojure.lang.IObj)
      (aload! mv 0)
      (.visitFieldInsn mv Opcodes/GETFIELD t "_meta" IPM-D)
      (invoke! mv clojure.lang.IObj "withMeta" clojure.lang.IPersistentMap)
      (op! mv ret)
      (end! mv))
    ;; reads: a declared key's field, else ext
    (let [mv (method cw pub "valAt" (mdesc clojure.lang.ILookup "valAt" Object))]
      (by-key! mv t ks 1 (fn [i]
                          (let [absent (Label.)]
                            (load-field mv t i) (astore! mv 2) (aload! mv 2) (load-absent mv t)
                            (jump! mv Opcodes/IF_ACMPEQ absent)
                            (aload! mv 2) (op! mv ret)
                            (.visitLabel mv absent)
                            (op! mv Opcodes/ACONST_NULL ret))))
      (load-ext mv t) (aload! mv 1) (invoke! mv clojure.lang.ILookup "valAt" Object) (op! mv ret)
      (end! mv))
    (let [mv (method cw pub "valAt" (mdesc clojure.lang.ILookup "valAt" Object Object))]
      (by-key! mv t ks 1 (fn [i]
                          (let [absent (Label.)]
                            (load-field mv t i) (astore! mv 3) (aload! mv 3) (load-absent mv t)
                            (jump! mv Opcodes/IF_ACMPEQ absent)
                            (aload! mv 3) (op! mv ret)
                            (.visitLabel mv absent)
                            (aload! mv 2) (op! mv ret))))
      (load-ext mv t) (aload! mv 1) (aload! mv 2) (invoke! mv clojure.lang.ILookup "valAt" Object Object) (op! mv ret)
      (end! mv))
    (let [mv (method cw pub "containsKey" (mdesc clojure.lang.Associative "containsKey" Object))]
      (by-key! mv t ks 1 (fn [i]
                          (let [absent (Label.)]
                            (load-field mv t i) (load-absent mv t)
                            (jump! mv Opcodes/IF_ACMPEQ absent)
                            (op! mv Opcodes/ICONST_1 Opcodes/IRETURN)
                            (.visitLabel mv absent)
                            (op! mv Opcodes/ICONST_0 Opcodes/IRETURN))))
      (load-ext mv t) (aload! mv 1) (invoke! mv clojure.lang.Associative "containsKey" Object) (op! mv Opcodes/IRETURN)
      (end! mv))
    (let [mv (method cw pub "entryAt" (mdesc clojure.lang.Associative "entryAt" Object))]
      (by-key! mv t ks 1 (fn [i]
                          (let [absent (Label.)]
                            (load-field mv t i) (load-absent mv t)
                            (jump! mv Opcodes/IF_ACMPEQ absent)
                            (aload! mv 1) (load-field mv t i)
                            (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/MapEntry" "create"
                                              (str "(" OBJ-D OBJ-D ")Lclojure/lang/MapEntry;") false)
                            (op! mv ret)
                            (.visitLabel mv absent)
                            (op! mv Opcodes/ACONST_NULL ret))))
      (load-ext mv t) (aload! mv 1) (invoke! mv clojure.lang.Associative "entryAt" Object) (op! mv ret)
      (end! mv))
    (let [mv (method cw pub "count" (mdesc clojure.lang.Counted "count"))]
      (aload! mv 0) (.visitFieldInsn mv Opcodes/GETFIELD t "cnt" "I")
      (op! mv Opcodes/IRETURN)
      (end! mv))
    ;; where keys are declared, T implements IKeywordLookup: getLookupThunk(k) answers T$K<i>
    ;; for the i-th declared key, else null, so a keyword's lookup of a declared key reads its
    ;; field, as on a defrecord
    (when (pos? n)
      (let [mv (method cw pub "getLookupThunk" (mdesc clojure.lang.IKeywordLookup "getLookupThunk" clojure.lang.Keyword))]
        (by-key! mv t ks 1 (fn [i]
                            (.visitTypeInsn mv Opcodes/NEW (thunk-name t i))
                            (op! mv Opcodes/DUP)
                            (.visitMethodInsn mv Opcodes/INVOKESPECIAL (thunk-name t i) "<init>" "()V" false)
                            (op! mv ret)))
        (op! mv Opcodes/ACONST_NULL ret)
        (end! mv)))
    (walk-methods! cw t n)
    (fold-methods! cw t n folds)
    (equality-methods! cw t n)
    ;; changes: this when nothing changed; else, for an assoc of a declared key with a guard,
    ;; G<i>.invoke(this, v), which returns or throws, then new T(this, i, v); else the whole
    ;; new map, through WRITES where it is set (with the one key an assoc or a without
    ;; writes), else as a plain map
    ;; private IPersistentMap assoc$i(Object v), per declared key i: assoc of K<i>, each in a
    ;; method of its own, so assoc stays small whatever the width, and the JIT inlines the
    ;; one a call site uses
    (dotimes [i n]
      (let [mv (method cw priv (str "assoc$" i) (str "(" OBJ-D ")" IPM-D))
            changed (Label.) unguarded (Label.) was (Label.)]
        (load-field mv t i) (aload! mv 1)
        (jump! mv Opcodes/IF_ACMPNE changed)
        (aload! mv 0) (op! mv ret)
        (.visitLabel mv changed)
        (static! mv t (str "G" i) IFN-D) (astore! mv 2)
        (aload! mv 2) (jump! mv Opcodes/IFNULL unguarded)
        (aload! mv 2) (aload! mv 0) (aload! mv 1)
        (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke" (str "(" OBJ-D OBJ-D ")" OBJ-D) true)
        (op! mv Opcodes/POP)
        ;; the count, one more where the field was absent
        (aload! mv 0) (.visitFieldInsn mv Opcodes/GETFIELD t "cnt" "I")
        (load-field mv t i) (load-absent mv t)
        (jump! mv Opcodes/IF_ACMPNE was)
        (op! mv Opcodes/ICONST_1 Opcodes/IADD)
        (.visitLabel mv was)
        (.visitVarInsn mv Opcodes/ISTORE 3)
        (.visitTypeInsn mv Opcodes/NEW t) (op! mv Opcodes/DUP)
        (aload! mv 0) (.visitFieldInsn mv Opcodes/GETFIELD t "_meta" IPM-D)
        (load-ext mv t)
        (.visitVarInsn mv Opcodes/ILOAD 3)
        (dotimes [j n] (if (= i j) (aload! mv 1) (load-field mv t j)))
        (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "<init>" (flat-desc n) false)
        (op! mv ret)
        (.visitLabel mv unguarded)
        (change! mv t 3 4 #(do (load-key mv t i) (aload! mv 1) 2))
        (load-entries mv t) (load-key mv t i) (aload! mv 1)
        (invoke! mv clojure.lang.IPersistentMap "assoc" Object Object)
        (astore! mv 5)
        (write! mv t 5 6 #(do (load-key mv t i) (aload! mv 1) 2))
        (end! mv)))
    (let [mv (method cw pub "assoc" (mdesc clojure.lang.IPersistentMap "assoc" Object Object))
          write (Label.)]
      (by-key! mv t ks 1 (fn [i]
                          (aload! mv 0) (aload! mv 2)
                          (.visitMethodInsn mv Opcodes/INVOKESPECIAL t (str "assoc$" i) (str "(" OBJ-D ")" IPM-D) false)
                          (op! mv ret)))
      (change! mv t 6 7 #(do (aload! mv 1) (aload! mv 2) 2))
      (load-ext mv t) (aload! mv 1) (aload! mv 2)
      (invoke! mv clojure.lang.IPersistentMap "assoc" Object Object)
      (astore! mv 4)
      (let [differ (Label.)]
        (aload! mv 4) (load-ext mv t) (jump! mv Opcodes/IF_ACMPNE differ)
        (aload! mv 0) (op! mv ret)
        (.visitLabel mv differ))
      (aload! mv 0) (aload! mv 4)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "withExt" (str "(" IPM-D ")" IPM-D) false)
      (astore! mv 3)
      (.visitLabel mv write)
      (write! mv t 3 5 #(do (aload! mv 1) (aload! mv 2) 2))
      (end! mv))
    (let [mv (method cw pub "without" (mdesc clojure.lang.IPersistentMap "without" Object))
          write (Label.)]
      (change! mv t 5 6 #(do (aload! mv 1) (static! mv t "REMOVED" OBJ-D) 2))
      (by-key! mv t ks 1 (fn [i]
                          (let [present (Label.)]
                            (load-field mv t i) (load-absent mv t)
                            (jump! mv Opcodes/IF_ACMPNE present)
                            (aload! mv 0) (op! mv ret)
                            (.visitLabel mv present)
                            (load-entries mv t) (aload! mv 1)
                            (invoke! mv clojure.lang.IPersistentMap "without" Object)
                            (astore! mv 2)
                            (jump! mv Opcodes/GOTO write))))
      (load-ext mv t) (aload! mv 1)
      (invoke! mv clojure.lang.IPersistentMap "without" Object)
      (astore! mv 3)
      (let [differ (Label.)]
        (aload! mv 3) (load-ext mv t) (jump! mv Opcodes/IF_ACMPNE differ)
        (aload! mv 0) (op! mv ret)
        (.visitLabel mv differ))
      (aload! mv 0) (aload! mv 3)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "withExt" (str "(" IPM-D ")" IPM-D) false)
      (astore! mv 2)
      (.visitLabel mv write)
      (write! mv t 2 4 #(do (aload! mv 1) (static! mv t "REMOVED" OBJ-D) 2))
      (end! mv))
    (let [mv (method cw pub "assocEx" (mdesc clojure.lang.IPersistentMap "assocEx" Object Object))]
      (load-entries mv t) (aload! mv 1) (aload! mv 2)
      (invoke! mv clojure.lang.IPersistentMap "assocEx" Object Object)
      (astore! mv 3)
      (write! mv t 3 4 (constantly 0))
      (end! mv))
    (let [mv (method cw pub "cons" (mdesc clojure.lang.IPersistentMap "cons" Object))]
      (change! mv t 5 6 #(do (aload! mv 1) 1))
      (load-entries mv t) (astore! mv 2)
      (aload! mv 2) (aload! mv 1)
      (invoke! mv clojure.lang.IPersistentCollection "cons" Object)
      (astore! mv 3)
      (return-this-if-same! mv 3 2)
      (write! mv t 3 4 (constantly 0))
      (end! mv))
    ;; public ITransientCollection asTransient() {
    ;;   c = CHG; if (c != null) return (ITransientCollection) c.invoke(this);
    ;;   w = WRITES; if (w == null) return ((IEditableCollection) withExt(ext)).asTransient();
    ;;   return (ITransientCollection) w.invoke(this); }
    (let [mv (method cw pub "asTransient" (mdesc clojure.lang.IEditableCollection "asTransient"))
          hooked (Label.)
          unchanged (Label.)]
      (static! mv t "CHG" IFN-D) (astore! mv 2)
      (aload! mv 2) (jump! mv Opcodes/IFNULL unchanged)
      (aload! mv 2) (aload! mv 0)
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke" (str "(" OBJ-D ")" OBJ-D) true)
      (cast! mv clojure.lang.ITransientCollection)
      (op! mv ret)
      (.visitLabel mv unchanged)
      (static! mv t "WRITES" IFN-D)
      (astore! mv 1)
      (aload! mv 1)
      (jump! mv Opcodes/IFNONNULL hooked)
      (load-entries mv t)
      (cast! mv clojure.lang.IEditableCollection)
      (invoke! mv clojure.lang.IEditableCollection "asTransient")
      (op! mv ret)
      (.visitLabel mv hooked)
      (aload! mv 1)
      (aload! mv 0)
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke" (str "(" OBJ-D ")" OBJ-D) true)
      (cast! mv clojure.lang.ITransientCollection)
      (op! mv ret)
      (end! mv))
    ;; public IPersistentCollection empty() { throw new UnsupportedOperationException(); }
    (let [mv (method cw pub "empty" (mdesc clojure.lang.IPersistentCollection "empty"))]
      (throw! mv UnsupportedOperationException "a value of a type has no empty value")
      (end! mv))
    ;; meta
    (doto (method cw pub "meta" (str "()" IPM-D))
      (aload! 0)
      (.visitFieldInsn Opcodes/GETFIELD t "_meta" IPM-D)
      (op! ret) (end!))
    (let [mv (method cw pub "withMeta" (mdesc clojure.lang.IObj "withMeta" clojure.lang.IPersistentMap))
          differ (Label.)]
      (aload! mv 1)
      (aload! mv 0)
      (.visitFieldInsn mv Opcodes/GETFIELD t "_meta" IPM-D)
      (jump! mv Opcodes/IF_ACMPNE differ)
      (aload! mv 0)
      (op! mv ret)
      (.visitLabel mv differ)
      (.visitTypeInsn mv Opcodes/NEW t)
      (op! mv Opcodes/DUP)
      (aload! mv 0)
      (aload! mv 1)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "<init>" (str "(L" t ";" IPM-D ")V") false)
      (op! mv ret)
      (end! mv))
    ;; serialization: out as a plain map; a hand-made stream naming T is refused
    (let [mv (method cw priv "writeReplace" (str "()" OBJ-D))]
      (aload! mv 0)
      (load-entries mv t)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "plain" (str "(" OBJ-D ")" OBJ-D) false)
      (op! mv ret)
      (end! mv))
    (doto (method cw priv "readObject" "(Ljava/io/ObjectInputStream;)V")
      (throw! java.io.InvalidObjectException "no key") (end!))
    ;; public static IPersistentMap create(IPersistentMap m) { return m; }  -- #T{..} reads plain
    (doto (method cw (bit-or pub stat) "create" (str "(" IPM-D ")" IPM-D))
      (aload! 0)
      (op! ret) (end!))
    ;; the listed interfaces' methods, and toString where given
    (doseq [[i m] (map-indexed vector plan)] (forwarder! cw t i m))
    (.visitEnd cw)
    (.toByteArray cw)))

(defn- draft-class-bytes [d t]
  (let [cw (ClassWriter. ClassWriter/COMPUTE_FRAMES)
        set-d "Ljava/util/Set;"]
    (.visit cw Opcodes/V1_8 (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_SUPER) d nil OBJ
            (into-array String ["java/util/function/BiConsumer" "java/util/function/Predicate"]))
    (.visitEnd (.visitField cw (bit-or Opcodes/ACC_PRIVATE Opcodes/ACC_FINAL) "marks" set-d nil nil))
    (doto (method cw Opcodes/ACC_PUBLIC "<init>" "()V")
      (.visitVarInsn Opcodes/ALOAD 0)
      (.visitMethodInsn Opcodes/INVOKESPECIAL OBJ "<init>" "()V" false)
      (.visitVarInsn Opcodes/ALOAD 0)
      (.visitMethodInsn Opcodes/INVOKESTATIC "java/util/concurrent/ConcurrentHashMap" "newKeySet"
                        "()Ljava/util/concurrent/ConcurrentHashMap$KeySetView;" false)
      (.visitFieldInsn Opcodes/PUTFIELD d "marks" set-d)
      (.visitInsn Opcodes/RETURN) (end!))
    ;; public void accept(Object key, Object check)
    (let [mv (method cw Opcodes/ACC_PUBLIC "accept" (str "(" OBJ-D OBJ-D ")V"))]
      (require-key! mv t 1 "marking a draft takes the type's key")
      (.visitVarInsn mv Opcodes/ALOAD 0)
      (.visitFieldInsn mv Opcodes/GETFIELD d "marks" set-d)
      (.visitVarInsn mv Opcodes/ALOAD 2)
      (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Set" "add" "(Ljava/lang/Object;)Z" true)
      (.visitInsn mv Opcodes/POP)
      (.visitInsn mv Opcodes/RETURN)
      (end! mv))
    ;; public static IFn gate() { return T.gate(); }
    (doto (method cw (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC) "gate" (str "()" IFN-D))
      (.visitMethodInsn Opcodes/INVOKESTATIC t "gate" (str "()" IFN-D) false)
      (.visitInsn Opcodes/ARETURN) (end!))
    ;; public boolean test(Object check)
    (doto (method cw Opcodes/ACC_PUBLIC "test" (str "(" OBJ-D ")Z"))
      (.visitVarInsn Opcodes/ALOAD 0)
      (.visitFieldInsn Opcodes/GETFIELD d "marks" set-d)
      (.visitVarInsn Opcodes/ALOAD 1)
      (.visitMethodInsn Opcodes/INVOKEINTERFACE "java/util/Set" "contains" "(Ljava/lang/Object;)Z" true)
      (.visitInsn Opcodes/IRETURN) (end!))
    (.visitEnd cw)
    (.toByteArray cw)))

(defonce ^:private counter (java.util.concurrent.atomic.AtomicLong.))

(defn fresh-name
  "A new class name, for a new type. Redefinition reuses the name."
  []
  (str "recognitum.proof.key_class.T" (.incrementAndGet ^java.util.concurrent.atomic.AtomicLong counter)))

(defn class-name
  "The class name for `type-name`, a symbol: `my.ns/T` -> `my.ns.T`. Every definition of the
  type names its value class so. Throws for a name that is not a symbol."
  ^String [type-name]
  (when-not (symbol? type-name)
    (throw (IllegalArgumentException. (str "a type's name is a symbol: " (pr-str type-name)))))
  (munge (.replace (str type-name) \/ \.)))

(defonce ^:private own-drafts
  (proxy [java.lang.ClassValue] []
    (computeValue [_] (java.util.concurrent.atomic.AtomicBoolean.))))

(defn- own-draft!
  "Records, on the class itself, that [[define]] made draft class `dc`."
  [^Class dc]
  (.set ^java.util.concurrent.atomic.AtomicBoolean (.get ^java.lang.ClassValue own-drafts dc) true))

(defn- marked?
  "Whether `draft` is of a draft class [[define]] made and records `check` as passed."
  [draft check]
  (boolean (and (some? draft)
                (.get ^java.util.concurrent.atomic.AtomicBoolean (.get ^java.lang.ClassValue own-drafts (class draft)))
                (.test ^java.util.function.Predicate draft check))))

(defn- refusal-of
  "A refusal of `kind`, whose message says `msg` of `x`, with `more` (`:method`, `:interfaces`)."
  [kind msg x more]
  (merge {:kind kind :message (str "refused definition: " msg ": " (pr-str x))} more))

(defn- refuse
  "Ends the analysis of a definition with [[refusal-of]] its arguments."
  [kind msg x & {:as more}]
  (throw (ex-info "refused" {::refusal (refusal-of kind msg x more)})))

(defn- method-of
  "`[name arity]` of the method named `n` with parameters `params`."
  [n params]
  [(symbol n) (count params)])

(defn- sig-method
  "`[name arity]` of the signature `[nm spec]`, the name spelled as the signature spells it."
  [[nm spec]]
  [(if (symbol? nm) nm (symbol nm)) (if (vector? spec) (count spec) spec)])

(defn- without-functions
  "`definition` as a refusal's message prints it: its signatures without their functions, so
  the words depend on no function."
  [definition]
  (if (and (map? definition) (map? (:methods definition)))
    (update definition :methods (comp vec keys))
    definition))

(def ^:private own
  "The [name parameter-types] of the methods T declares for itself, statics included."
  #{["claim" [(class (object-array 0)) Object]] ["install" [Object Object Object (class (object-array 0)) Object]] ["gate" []]
    ["create" [clojure.lang.IPersistentMap]] ["delta$" [Object Object]] ["index$" [Object]] ["plain" [Object]] ["withExt" [clojure.lang.IPersistentMap]]
    ["writeReplace" []] ["getLookupThunk" [clojure.lang.Keyword]]
    ["readObject" [java.io.ObjectInputStream]] ["meta" []] ["withMeta" [clojure.lang.IPersistentMap]]
    ["asTransient" []] ["valAt" [Object]] ["valAt" [Object Object]] ["containsKey" [Object]]
    ["entryAt" [Object]] ["count" []] ["seq" []] ["iterator" []] ["keyIterator" []] ["valIterator" []] ["assoc" [Object Object]]
    ["assocEx" [Object Object]] ["without" [Object]] ["cons" [Object]] ["empty" []]})

(defn- own?
  "Whether T declares a method `n` of `params` for itself: in [[own]], or the assoc of one
  declared key."
  [n params]
  (or (contains? own [n params])
      (and (= [Object] params) (some? (re-matches #"assoc\$\d+" n)))))

(defn- implemented?
  "Whether T has a method `n` of `params` without the definition: its own or its map's."
  [n params]
  (or (own? n params)
      (try (.getMethod clojure.lang.APersistentMap n (into-array Class params)) true
           (catch NoSuchMethodException _ false))))

(defn- class-implemented?
  "Whether a class T extends, or T itself, declares method `n` of `params`: a body that wins
  over every interface's default."
  [n params]
  (or (own? n params)
      (try (not (.isInterface (.getDeclaringClass (.getMethod clojure.lang.APersistentMap n (into-array Class params)))))
           (catch NoSuchMethodException _ false))))

(defn- interface-methods
  "The instance methods interface `c` declares or inherits, as [[name params] Method] pairs."
  [^Class c]
  (for [^Method m (.getMethods c)
        :when (not (Modifier/isStatic (.getModifiers m)))]
    [[(.getName m) (vec (.getParameterTypes m))] m]))

(defn- members
  "The instance methods `c` declares or inherits, as [[name params] Method] pairs; of
  `Object`, `toString` alone. Refuses a class that is neither an interface nor `Object`."
  [^Class c]
  (cond
    (= c Object)     [[["toString" []] (.getMethod Object "toString" (make-array Class 0))]]
    (.isInterface c) (interface-methods c)
    :else            (refuse :not-an-interface "not an interface" c :interfaces [c])))

(def ^:private map-methods
  "The methods of the interfaces T has as a map, by [name params]: their defaults compete
  with a listed interface's."
  (group-by first (mapcat interface-methods (filter #(.isInterface ^Class %) (supers clojure.lang.APersistentMap)))))

(defn- maximal
  "The methods of `ms` whose declaring interface no other declaring interface of `ms` extends."
  [ms]
  (let [owners (set (map #(.getDeclaringClass ^Method %) ms))]
    (remove (fn [^Method m]
              (let [a (.getDeclaringClass m)]
                (some (fn [^Class b] (and (not= a b) (.isAssignableFrom a b))) owners)))
            ms)))

(def ^:private draft-interfaces
  "The interfaces every draft class implements."
  [java.util.function.BiConsumer java.util.function.Predicate])

(defn- plan
  "The methods of `definition` that T forwards, as [interfaces plan]: each entry
  {:name :params :ret :f}, `:f` nil where no function implements it. Refuses a signature no
  listed interface declares, one that matches more than one method or names a method T has
  without the definition, two signatures of one method, `equals` and `hashCode`, two
  listed methods of one name and parameters with different return types (among the methods
  T does not have as a map), a method with no function whose most specific declarations
  give more than one default body, and an interface that a draft implements.

  A method with no function and no default body among its most specific declarations
  forwards to nothing, and throws; one with exactly one keeps that body."
  [{:keys [interfaces methods] :as definition}]
  (when-not (and (map? definition) (or (nil? interfaces) (sequential? interfaces))
                 (or (nil? methods) (map? methods)) (every? class? interfaces))
    (refuse :malformed "not {:interfaces [class ...] :methods {signature f}}" (without-functions definition)))
  (let [ks (:keys definition)]
    (when-not (or (nil? ks)
                  (and (sequential? ks) (every? keyword? ks) (= (count ks) (count (distinct ks)))))
      (refuse :malformed "the keys are distinct keywords" ks))
    (when (> (count ks) max-keys)
      (refuse :too-many-keys (str "a definition declares at most " max-keys " keys") (count ks))))
  (doseq [^Class i interfaces
          :when (and (not= Object i) (some #(.isAssignableFrom i %) draft-interfaces))]
    (refuse :draft-interface "a draft implements this interface, and a draft implements none of its definition's" i
            :interfaces [i]))
  (let [listed  (group-by first (mapcat members (distinct interfaces)))
        by-sig  (into {} (for [[k pairs] listed
                               :let [ms (distinct (map second pairs))]]
                           (do (when (and (not (apply implemented? k))
                                          (< 1 (count (distinct (map #(.getReturnType ^Method %) ms)))))
                                 (refuse :clash "two listed methods differ only in return type" k
                                         :method (apply method-of k)
                                         :interfaces (vec (distinct (map #(.getDeclaringClass ^Method %) ms)))))
                               [k (first ms)])))
        resolve (fn [[nm spec :as sig]]
                  (when-not (and (vector? sig) (= 2 (count sig)) (or (symbol? nm) (string? nm))
                                 (or (nat-int? spec) (and (vector? spec) (every? class? spec))))
                    (refuse :malformed "a signature is [name arity] or [name [class ...]]" sig))
                  (let [n (str nm)]
                    (when (#{"equals" "hashCode"} n)
                      (refuse :equality "a value's equality is its map's" sig :method (sig-method sig)))
                    (let [found (filter (fn [[[mn ps]]]
                                          (and (= n mn) (if (vector? spec) (= spec ps) (= spec (count ps)))))
                                        by-sig)]
                      (case (count found)
                        0 (refuse :undeclared "no listed interface declares" sig :method (sig-method sig))
                        1 (let [[k] (first found)]
                            (when (and (apply implemented? k) (not= k ["toString" []]))
                              (refuse :map-method "a value has this method without the definition" sig
                                      :method (sig-method sig)))
                            k)
                        (refuse :ambiguous "more than one method matches" sig :method (sig-method sig))))))
        given   (reduce (fn [acc [sig f]]
                          (let [k (resolve sig)]
                            (when-not (or (nil? f) (ifn? f))
                              (refuse :not-a-function "not a function" sig :method (sig-method sig)))
                            (when (contains? acc k)
                              (refuse :duplicate "two signatures name one method" sig :method (sig-method sig)))
                            (assoc acc k f)))
                        {} methods)
        ;; the default bodies a call of `k` could run, where no class T extends declares it
        defaults (fn [k]
                   (if (apply class-implemented? k)
                     []
                     (filter #(.isDefault ^Method %)
                             (maximal (distinct (map second (concat (listed k) (map-methods k))))))))
        _       (doseq [k (keys by-sig)
                        :when (not (contains? given k))
                        :let [ds (defaults k)]
                        :when (< 1 (count ds))]
                  (refuse :clash
                          (str "the interfaces " (str/join " and " (map #(.getName (.getDeclaringClass ^Method %)) ds))
                               " give default bodies of " (first k) " and the definition gives no function for it")
                          k
                          :method (apply method-of k)
                          :interfaces (vec (map #(.getDeclaringClass ^Method %) ds))))
        sigs    (distinct (concat (for [k (keys by-sig)
                                        :when (and (not (apply implemented? k)) (empty? (defaults k)))]
                                    k)
                                  (keys given)))]
    [(vec (remove #(= Object %) (distinct interfaces)))
     (vec (for [[n ps :as k] sigs
                :let [^Method m (by-sig k)]]
            {:name n :params ps :ret (.getReturnType m) :f (given k)}))]))

(defonce ^:private removed
  (reify Object (toString [_] "the removed key")))

(def ^:private none
  "What a lookup answers for a key a map lacks: an object no map holds."
  (Object.))

(defn- pair-change
  "`[k v]` as a change of `old`, flat, or nil where it changes nothing: `v` identical to
  `old`'s entry, or `removed` for a key `old` lacks."
  [^clojure.lang.ILookup old k v]
  (let [o (.valAt old k none)]
    (when-not (if (identical? v removed) (identical? o none) (identical? v o))
      (doto (object-array 2) (aset 0 k) (aset 1 v)))))

(defn- entries-change
  "The entries of `es` that change `old`, flat, or nil: `es` an iterator over the entries of a
  map, so no key comes twice. A value `removed` removes its key."
  [^clojure.lang.ILookup old n ^java.util.Iterator es]
  (let [a (object-array (* 2 n))]
    (loop [i 0]
      (if (.hasNext es)
        (let [^java.util.Map$Entry e (.next es)
              k (.getKey e) v (.getValue e)
              o (.valAt old k none)]
          (if (if (identical? v removed) (identical? o none) (identical? v o))
            (recur i)
            (do (aset a i k) (aset a (unchecked-inc i) v) (recur (unchecked-add i 2)))))
        (cond (zero? i) nil
              (== i (alength a)) a
              :else (java.util.Arrays/copyOf a i))))))

;; What a change transient answers itself: `net` the pairs it holds that change the value it
;; was made from, which persistent! hands to that value's cons.
(definterface ^:private ChangeSlots
  (live [])
  (^long at [k])
  (now [k])
  (add [k v])
  (put [k v])
  (net [target]))

(defn- conj-change
  "What `(conj old o)` changes, flat, or nil, read as `APersistentMap.cons` reads `o`: an entry,
  a vector pair, or a seq of entries, a later entry of a key replacing an earlier one."
  [^clojure.lang.ILookup old o]
  (cond
    ;; persistent! of a transient over `old`, which hands itself
    (instance? ChangeSlots o) (.net ^ChangeSlots o old)
    (instance? java.util.Map$Entry o)
    (pair-change old (.getKey ^java.util.Map$Entry o) (.getValue ^java.util.Map$Entry o))
    (instance? clojure.lang.IPersistentVector o)
    (let [^clojure.lang.IPersistentVector o o]
      (when-not (== 2 (.count o))
        (throw (IllegalArgumentException. "Vector arg to map conj must be a pair")))
      (pair-change old (.nth o 0) (.nth o 1)))
    (instance? clojure.lang.IPersistentMap o)
    (entries-change old (count o) (.iterator ^Iterable o))
    :else
    (let [m (loop [m (transient {}) s (seq o)]
              (if s
                (let [^java.util.Map$Entry e (first s)] (recur (assoc! m (.getKey e) (.getValue e)) (next s)))
                (persistent! m)))]
      (entries-change old (count m) (.iterator ^Iterable m)))))

(deftype ^:private ChangeTransient [^clojure.lang.IPersistentCollection old
                                    ^:unsynchronized-mutable ^objects over
                                    ^:unsynchronized-mutable ^long size
                                    ^:unsynchronized-mutable ^long cnt
                                    ^:unsynchronized-mutable done]
  ;; `over` holds the pairs it was told, flat, each key once, the last value or `removed`
  ;; winning; `size` the slots used; `cnt` the count now
  clojure.lang.ITransientMap
  (assoc [this k v] (.put this k v) this)
  (without [this k]
    (.live this)
    (let [i (.at this k)
          o (if (neg? i) (.valAt ^clojure.lang.ILookup old k none) (aget over (inc i)))]
      (when-not (or (identical? o none) (identical? o removed))
        (set! cnt (dec cnt))
        (if (neg? i) (.add this k removed) (aset over (inc i) removed))))
    this)
  (conj [this o]
    (.live this)
    (cond (instance? java.util.Map$Entry o) (.put this (.getKey ^java.util.Map$Entry o) (.getValue ^java.util.Map$Entry o))
          (instance? clojure.lang.IPersistentVector o)
          (let [^clojure.lang.IPersistentVector o o]
            (when-not (== 2 (.count o))
              (throw (IllegalArgumentException. "Vector arg to map conj must be a pair")))
            (.put this (.nth o 0) (.nth o 1)))
          :else (loop [s (seq o)]
                  (when s
                    (let [^java.util.Map$Entry e (first s)] (.put this (.getKey e) (.getValue e)))
                    (recur (next s)))))
    this)
  (persistent [this]
    (.live this)
    (set! done true)
    (if (zero? size)
      old
      (.cons old this)))
  (count [this] (.live this) (int cnt))
  (valAt [this k] (.live this) (let [v (.now this k)] (if (identical? v none) nil v)))
  (valAt [this k nf] (.live this) (let [v (.now this k)] (if (identical? v none) nf v)))
  clojure.lang.ITransientAssociative2
  (containsKey [this k] (.live this) (not (identical? none (.now this k))))
  (entryAt [this k] (.live this) (let [v (.now this k)] (when-not (identical? v none) (clojure.lang.MapEntry/create k v))))
  ChangeSlots
  (live [_] (when done (throw (IllegalAccessError. "Transient used after persistent! call"))))
  (at [_ k]
    (loop [i 0]
      (cond (>= i size) -1
            (clojure.lang.Util/equiv k (aget over i)) i
            :else (recur (+ i 2)))))
  (now [this k]
    (let [i (.at this k)]
      (if (neg? i)
        (.valAt ^clojure.lang.ILookup old k none)
        (let [v (aget over (inc i))] (if (identical? v removed) none v)))))
  (add [_ k v]
    (when (== size (alength over))
      (set! over (java.util.Arrays/copyOf over (int (* 2 size)))))
    (aset over size k)
    (aset over (inc size) v)
    (set! size (+ size 2)))
  (net [_ target]
    ;; the pairs that change `old`, flat, or nil; only `old` itself takes them
    (when-not (identical? target old)
      (throw (IllegalArgumentException. "a transient's changes apply only to the value it was made from")))
    (let [a (object-array size)]
      (loop [i 0 j 0]
        (if (< i size)
          (let [k (aget over i) v (aget over (inc i)) o (.valAt ^clojure.lang.ILookup old k none)]
            (if (if (identical? v removed) (identical? o none) (identical? v o))
              (recur (+ i 2) j)
              (do (aset a j k) (aset a (inc j) v) (recur (+ i 2) (+ j 2)))))
          (cond (zero? j) nil
                (== j size) a
                :else (java.util.Arrays/copyOf a (int j)))))))
  (put [this k v]
    (.live this)
    (let [i (.at this k)
          o (if (neg? i) (.valAt ^clojure.lang.ILookup old k none) (aget over (inc i)))]
      (when (or (identical? o none) (identical? o removed)) (set! cnt (inc cnt)))
      (if (neg? i) (.add this k v) (aset over (inc i) v)))))

(defn- change-transient
  "A transient over `old` that keeps only what it is told; its persistent! is one
  `(conj old this)`, so one call of the change guard with the net change. Reads
  answer as a transient over `old`'s map would."
  [^clojure.lang.IPersistentCollection old]
  (ChangeTransient. old (object-array 8) 0 (.count old) false))

(defn- changes-fn
  "CHG for the change guard `cg`: what T's changes call in place of the write. With `old` and
  the change, it answers the change as flat pairs k, v (`removed` for a removal), after
  `(cg old changes)` returned, or nil where nothing changes, calling nothing; T makes the
  value from `old` and those pairs. With `old` alone, a transient over it."
  [^clojure.lang.IFn cg]
  (let [guarded (fn [old ^objects ch]
                  (when ch
                    (.invoke cg old (clojure.lang.PersistentArrayMap. ch))
                    ch))]
    (fn
      ([old] (change-transient old))
      ([old o] (guarded old (conj-change old o)))
      ([old k v] (guarded old (pair-change old k v))))))

(defn- handle
  "The handle of one emitted class pair, whose value class declares the keys `ks`. A reify,
  not a map: nothing walks into it."
  [^Class vc ^Class dc ^clojure.lang.IFn make key ks]
  (let [draft-ctor (.getConstructor dc (make-array Class 0))
        install    (.getMethod vc "install" (into-array Class [Object Object Object (class (object-array 0)) Object]))
        gate       (.getMethod vc "gate" (make-array Class 0))
        ;; T's changes call the first function, always with the value itself as `old`.
        ;; `installed` hands the second to callers without the key, so a write through it
        ;; starts only from a value of this definition, and it has no four-argument arity: the
        ;; key a caller names is trusted only where T names it. `guards` is nil, or one guard
        ;; or nil per declared key; `changes` nil, or what T's changes call in place of the
        ;; write, which holds no key: T makes the value.
        install!   (fn [write guards changes]
                     (let [own! (fn [old]
                                  (when-not (.isInstance vc old)
                                    (throw (IllegalArgumentException. "a write starts from a value of its type"))))]
                       (.invoke install nil (object-array [key
                                                           (fn ([old] (proof/checked-transient old write))
                                                               ([old entries] (write old entries))
                                                               ([old entries k v] (write old entries k v)))
                                                           (fn ([old] (own! old) (proof/checked-transient old write))
                                                               ([old entries] (own! old) (write old entries))
                                                               ([a b c] (write a b c)))
                                                           guards
                                                           changes])))
                     nil)
        guards!    (fn [key-write]
                     ;; refused before key-write is asked, so a second install asks nothing
                     (when (.invoke gate nil (object-array 0))
                       (throw (SecurityException. "writes already installed")))
                     (object-array
                      (for [k ks
                            :let [g (key-write k)]]
                        ;; fn?, not ifn?: a guard permits by returning, so a keyword, map,
                        ;; set or var, which returns for any argument, would permit every write
                        (if (or (nil? g) (fn? g))
                          g
                          (throw (IllegalArgumentException. (str "a key write answers nil or a guard made by fn: " (pr-str k))))))))]
    (reify proof/Handle
      (seal [_ m]
        (.invoke make key (proof/plain-map m)))
      (proven? [_ v] (.isInstance vc v))
      (install-write! [_ write] (install! write nil nil))
      (install-write! [_ write key-write] (install! write (guards! key-write) nil))
      (install-write! [_ write key-write change-guard]
        (when-not (fn? change-guard)
          (throw (IllegalArgumentException. "a change guard is made by fn")))
        (install! write (guards! key-write) (changes-fn change-guard)))
      (open [_] (.newInstance draft-ctor (object-array 0)))
      (mark! [_ draft check]
        (when-not (.isInstance dc draft) (throw (IllegalArgumentException. "not a draft of this type")))
        (.accept ^java.util.function.BiConsumer draft key check)
        nil)
      (passed? [_ draft check]
        (and (.isInstance dc draft) (.test ^java.util.function.Predicate draft check)))
      (classes [_] [vc dc])
      (capabilities [_] [key]))))

(defn- print-preferences
  "Where `print-method` or `print-dup` has an entry for a listed interface or one of its
  supertypes, the preferences of the map's entry, and of `Proven`'s, over it, as
  [multimethod-name multimethod winner entry]: else a value of both would match two entries
  and print neither."
  [ifaces]
  (for [[nm ^MultiFn mf] [["print-method" print-method] ["print-dup" print-dup]]
        k (keys (methods mf))
        :when (and (class? k) (not= Object k) (not (isa? clojure.lang.IPersistentMap k))
                   (some #(isa? % k) ifaces))
        winner [clojure.lang.IPersistentMap recognitum.proof.Proven]]
    [nm mf winner k]))

(defn- outranked
  "The refusal where multimethod `nm` already prefers interface `k`'s entry to the map's."
  [nm k]
  (refusal-of :clash (str nm " prefers this interface's entry to the map's, so a value could not print as its map") k
              {:interfaces [k]}))

(defn- check-outranked
  "Refuses where one of `prefs` cannot be set because the entry is already preferred over the
  winner. Tried on a copy of each multimethod's preferences, so it changes none."
  [prefs]
  (doseq [[nm group] (group-by first prefs)
          :let [^MultiFn mf (second (first group))
                copy (MultiFn. nm (.-dispatchFn mf) (.-defaultDispatchVal mf) (.-hierarchy mf))]]
    (doseq [[x ys] (.getPreferTable mf), y ys] (.preferMethod copy x y))
    (doseq [[_ _ winner k] group]
      (try (.preferMethod copy winner k)
           (catch IllegalStateException _ (throw (ex-info "refused" {::refusal (outranked nm k)})))))))

(defn- analysis
  "What defining `definition` takes, `{:interfaces :plan :prefs}`, or why it is refused,
  `{:refusal r}`. Defines and sets nothing. Besides [[plan]]'s refusals, refuses a listed
  interface whose name now loads another class (an interface defined again after the
  definition named it), which would leave values outside the one listed, and a print
  preference that cannot be set."
  [definition]
  (try
    (let [[ifaces plan] (plan (or definition {}))
          loader (DynamicClassLoader. (RT/baseLoader))]
      (doseq [^Class i ifaces]
        (when-not (identical? i (try (Class/forName (.getName i) false loader)
                                     (catch ClassNotFoundException _ nil)))
          (refuse :reloaded-interface "the interface's name now names another class" i :interfaces [i])))
      (let [prefs (print-preferences ifaces)]
        (check-outranked prefs)
        {:interfaces ifaces :plan plan :prefs prefs :keys (vec (:keys definition))}))
    (catch clojure.lang.ExceptionInfo e
      (if-let [r (::refusal (ex-data e))] {:refusal r} (throw e)))))

(defn- refusal
  "Nil where [[define]] accepts `definition`, else the refusal it throws."
  [definition]
  (:refusal (analysis definition)))

(defn- prefer-print-as-map!
  "Sets `prefs`, which [[analysis]] checked. One set meanwhile in the other direction refuses."
  [prefs]
  (doseq [[nm ^MultiFn mf winner k] prefs]
    (try (.preferMethod mf winner k)
         (catch IllegalStateException _
           (let [r (outranked nm k)] (throw (ex-info (:message r) r)))))))

(defn- define
  "Refuses, defining nothing, where [[analysis]] does, throwing the refusal as `ex-info` data
  with its message. The refusal is checked before T is defined, so it leaves no class under
  the type's name."
  [type-name definition]
  (let [{ks :keys :keys [refusal interfaces plan prefs]} (analysis definition)
        _      (when refusal (throw (ex-info (:message refusal) refusal)))
        ^String n (if type-name (class-name type-name) (fresh-name))
        t      (.replace n \. \/)
        d      (str t "$Draft")
        loader (DynamicClassLoader. (RT/baseLoader))
        _      (prefer-print-as-map! prefs)
        vc     (.defineClass loader n (value-class-bytes t interfaces plan ks) nil)
        _      (dotimes [i (count ks)]
                 (.defineClass loader (.replace ^String (thunk-name t i) \/ \.) (thunk-bytes t i) nil))
        _      (.defineClass loader (.replace ^String (iter-name t) \/ \.) (iter-bytes t ks) nil)]
    (let [dc  (.defineClass loader (.replace d \/ \.) (draft-class-bytes d t) nil)
          _   (own-draft! dc)
          make (.newInstance (.getConstructor ^Class (.defineClass loader (str n "$New") (maker-bytes t) nil)
                                              (make-array Class 0))
                             (object-array 0))
          key (.invoke (.getMethod ^Class vc "claim" (into-array Class [(class (object-array 0)) Object]))
                       nil (object-array [(object-array (map :f plan)) removed]))]
      (handle vc dc make key ks))))

(def strategy
  "Each `define-type` emits T and T$Draft into a new loader and claims T's key. The same
  name again is redefinition: a new class pair with a new key. A refused definition throws
  and leaves the type as it was: no handle exists for it, and no key is claimed."
  (reify proof/Strategy
    (installed [_ value-class]
      (.invoke (.getMethod ^Class value-class "gate" (make-array Class 0)) nil (object-array 0)))
    (define-type [_ type-name] (define type-name nil))
    (define-type [_ type-name definition] (define type-name definition))
    (refusal [_ definition] (refusal definition))
    (class-name [_ type-name] (when type-name (class-name type-name)))
    (removed [_] removed)
    (marked? [_ draft check] (marked? draft check))))
