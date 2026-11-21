(ns recognitum.proof.key-class.emit
  "The bytecode of the classes that one definition of the key-class strategy is made of:

  - T, the value class;
  - T$Draft, its draft class;
  - T$I, the iterator over a T's entries, keys or values;
  - T$New, the maker, which calls T's constructor;
  - T$K<i>, the lookup thunk of the i-th declared key.

  Each emitter takes `t`, T's internal name (`my/ns/T`), and what the definition declares,
  and answers the class's bytes; it defines nothing."
  (:require [recognitum.proof])
  (:import [clojure.asm ClassWriter Opcodes Type Label MethodVisitor]
           [clojure.lang RT]))

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
  a return or a jump; the code emitted after them runs for any other key. Keywords are
  interned, so identity is their equality. Past eight keys, a lookupswitch on the keyword's
  hasheq picks the keys to compare, as `case` does for a defrecord."
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

(defn- invoke-ifn!
  "IFn.invoke of `arity` Objects, on the IFn and the arguments on the stack."
  [^MethodVisitor mv arity]
  (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke"
                    (str "(" (apply str (repeat arity OBJ-D)) ")" OBJ-D) true))

(defn- write!
  "w = WRITES; if (w != null) return (IPersistentMap) w.invoke(this, local[e], more...);
   return (IPersistentMap) plain(local[e]);
  `more!` pushes the further arguments and returns how many it pushed. Local `w` is scratch."
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
      (invoke-ifn! mv (+ 2 k)))
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
      (invoke-ifn! mv (inc k)))
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

(defn- return-this-if-ext!
  "if (local[slot] == this.ext) return this;"
  [^MethodVisitor mv t slot]
  (let [differ (Label.)]
    (aload! mv slot) (load-ext mv t) (jump! mv Opcodes/IF_ACMPNE differ)
    (aload! mv 0) (op! mv Opcodes/ARETURN)
    (.visitLabel mv differ)))

(defn- map-entry!
  "MapEntry.create(k, v) of the key and the value on the stack."
  [^MethodVisitor mv]
  (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/MapEntry" "create"
                    (str "(" OBJ-D OBJ-D ")Lclojure/lang/MapEntry;") false))

(defn- super-init!
  "super(), APersistentMap's constructor, on this."
  [^MethodVisitor mv]
  (aload! mv 0)
  (.visitMethodInsn mv Opcodes/INVOKESPECIAL (iname clojure.lang.APersistentMap) "<init>" "()V" false))

(defn- intern-keys!
  "K<j> = Keyword.intern(ns, name) for the j-th key of `ks`, K<j> a static field of the class
  `owner`."
  [^MethodVisitor mv owner ks]
  (doseq [[j k] (map-indexed vector ks)]
    (if-let [kns (namespace k)] (.visitLdcInsn mv kns) (op! mv Opcodes/ACONST_NULL))
    (.visitLdcInsn mv (name k))
    (.visitMethodInsn mv Opcodes/INVOKESTATIC "clojure/lang/Keyword" "intern"
                      "(Ljava/lang/String;Ljava/lang/String;)Lclojure/lang/Keyword;" false)
    (.visitFieldInsn mv Opcodes/PUTSTATIC owner (str "K" j) OBJ-D)))

(defn- no-key-message
  "What T's constructor says when called without the access key: the type, by its class name, and
  then `instead`, the words its definition handed down, or, where it handed down none, that a
  value of the type is made only through recognitum."
  [t instead]
  (str (.replace ^String t \/ \.) "'s constructor takes a key only recognitum holds: "
       (or instead "a value of this type is made only through recognitum")))

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
     f = (IFn) FNS[idx];
     if (f == null) throw new UnsupportedOperationException(\"no function implements <name>\");
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
          (invoke-ifn! mv (inc n)))
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

(defn maker-bytes
  "T$New's bytes: an AFn whose invoke(key, data) returns new T(key, data), so the handle calls
  T's constructor without reflection; of an unsealed T, invoke(key, data, mem) returns
  new T(key, data, mem). It holds no access key: T's constructor still checks the one it is
  given."
  [t unsealed?]
  (let [cw (ClassWriter. ClassWriter/COMPUTE_FRAMES)
        afn (iname clojure.lang.AFn)]
    (.visit cw Opcodes/V1_8 (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL Opcodes/ACC_SUPER) (str t "$New") nil afn
            (make-array String 0))
    (doto (method cw Opcodes/ACC_PUBLIC "<init>" "()V")
      (aload! 0)
      (.visitMethodInsn Opcodes/INVOKESPECIAL afn "<init>" "()V" false)
      (op! Opcodes/RETURN) (end!))
    (let [args (if unsealed? 3 2)
          desc (apply str (repeat args OBJ-D))
          mv   (method cw Opcodes/ACC_PUBLIC "invoke" (str "(" desc ")" OBJ-D))]
      (.visitTypeInsn mv Opcodes/NEW t)
      (op! mv Opcodes/DUP)
      (dotimes [i args] (aload! mv (inc i)))
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "<init>" (str "(" desc ")V") false)
      (op! mv Opcodes/ARETURN)
      (end! mv))
    (.visitEnd cw)
    (.toByteArray cw)))

(defn thunk-name
  "The internal name of the lookup thunk of the i-th declared key of T, `t`."
  [t i]
  (str t "$K" i))

(defn thunk-bytes
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

;; HotSpot does not JIT-compile a method of more than 8000 bytes of bytecode. Past this many
;; keys, the longest method of T that holds every key's code inline would pass that size.
(def ^:private inline-keys
  "The most declared keys for which each method of T holds every key's code inline. A T of
  more keys is wide: it reads a declared key's field through field$(i), with the index from
  index$, counts its present fields in present$(), and walks its fields in chunks, each a
  private method of its own."
  160)

(defn- wide? [n] (> n inline-keys))

(defn- chunks
  "The key index ranges [lo hi) in which a wide T of `n` keys walks its fields: the fewest
  ranges, of near-equal size, that each hold at most [[inline-keys]] keys."
  [n]
  (let [c (max 1 (quot (+ n inline-keys -1) inline-keys))
        size (max 1 (quot (+ n c -1) c))]
    (for [lo (range 0 n size)] [lo (min n (+ lo size))])))

(defn- load-field-at
  "this.field$(local[slot]): of a wide T, the field of the declared key at the index in int local `slot`."
  [^MethodVisitor mv t slot]
  (aload! mv 0)
  (.visitVarInsn mv Opcodes/ILOAD (int slot))
  (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "field$" (str "(I)" OBJ-D) false))

(defn- by-field!
  "Emits (body load!) for a key in local `slot` that T declares, where `load!` pushes that
  key's field and the body ends in a return or a jump; the code emitted after it runs for any
  other key. Where T is not wide, this is [[by-key!]] with one body per key. Where T is wide,
  one body reads the field at index$(key), kept in int local `i`, so the method's size does
  not grow with the keys."
  [^MethodVisitor mv t ks slot i body]
  (if (wide? (count ks))
    (let [undeclared (Label.)]
      (aload! mv slot)
      (.visitMethodInsn mv Opcodes/INVOKESTATIC t "index$" (str "(" OBJ-D ")I") false)
      (.visitVarInsn mv Opcodes/ISTORE (int i))
      (.visitVarInsn mv Opcodes/ILOAD (int i))
      (jump! mv Opcodes/IFLT undeclared)
      (body #(load-field-at mv t i))
      (.visitLabel mv undeclared))
    (by-key! mv t ks slot (fn [j] (body #(load-field mv t j))))))

(defn- flat-desc
  "The descriptor of T's constructor taking meta, ext, the count and the n fields."
  [n]
  (str "(" IPM-D IPM-D "I" (apply str (repeat n OBJ-D)) ")V"))

(defn iter-name
  "The internal name of the iterator class of T, `t`."
  [t]
  (str t "$I"))

(defn- iter-load!
  "this.<nm>, of descriptor `d`, of the iterator class `c`."
  [^MethodVisitor mv c nm d]
  (aload! mv 0) (.visitFieldInsn mv Opcodes/GETFIELD c nm d))

(defn- iter-field!
  "this.t.f<j>: field f<j> of the T, `t`, that the iterator class `c` walks."
  [^MethodVisitor mv c t j]
  (iter-load! mv c "t" (str "L" t ";")) (.visitFieldInsn mv Opcodes/GETFIELD t (str "f" j) OBJ-D))

(defn- table-switch!
  "A tableswitch on the int in local `slot`: (body j) for each j in [0 n), each body ending in
  a return or a jump. An index outside [0 n) falls through; where n is 0, nothing is emitted."
  [^MethodVisitor mv n slot body]
  (when (pos? n)
    (let [labels (vec (repeatedly n #(Label.))) dflt (Label.)]
      (.visitVarInsn mv Opcodes/ILOAD (int slot))
      (.visitTableSwitchInsn mv 0 (dec n) dflt (into-array Label labels))
      (doseq [j (range n)] (.visitLabel mv (labels j)) (body j))
      (.visitLabel mv dflt))))

(defn- iter-fields!
  "Declares T$I's fields: t, the T it walks; ext; mode; i, the index of the next field; it,
  ext's iterator; and the static K<j> of each of the n declared keys."
  [^ClassWriter cw t n]
  (let [T-D  (str "L" t ";")
        IT-D "Ljava/util/Iterator;"
        priv Opcodes/ACC_PRIVATE
        fin  Opcodes/ACC_FINAL]
    (doseq [[acc nm d] (concat [[(bit-or priv fin) "t" T-D] [(bit-or priv fin) "ext" IPM-D] [(bit-or priv fin) "mode" "I"]
                                [priv "i" "I"] [priv "it" IT-D]]
                               (for [j (range n)] [(bit-or priv Opcodes/ACC_STATIC fin) (str "K" j) OBJ-D]))]
      (.visitEnd (.visitField cw (int acc) nm d nil nil)))))

(defn- iter-static-initializer!
  "static { K<j> = Keyword.intern(ns, name); } of T$I, `c`, for each of the keys `ks`."
  [^ClassWriter cw c ks]
  (let [mv (method cw Opcodes/ACC_STATIC "<clinit>" "()V")]
    (intern-keys! mv c ks)
    (op! mv Opcodes/RETURN) (end! mv)))

(defn- iter-constructor!
  "T$I(T t, IPersistentMap ext, int mode), package-private: T makes it."
  [^ClassWriter cw c t]
  (let [T-D (str "L" t ";")]
    (doto (method cw 0 "<init>" (str "(" T-D IPM-D "I)V"))
      (aload! 0) (.visitMethodInsn Opcodes/INVOKESPECIAL OBJ "<init>" "()V" false)
      (aload! 0) (aload! 1) (.visitFieldInsn Opcodes/PUTFIELD c "t" T-D)
      (aload! 0) (aload! 2) (.visitFieldInsn Opcodes/PUTFIELD c "ext" IPM-D)
      (aload! 0) (.visitVarInsn Opcodes/ILOAD 3) (.visitFieldInsn Opcodes/PUTFIELD c "mode" "I")
      (op! Opcodes/RETURN) (end!))))

(defn- iter-field-method!
  "private boolean field() of T$I, `c`, over the n fields of T, `t`: moves i past absent
  fields, and answers whether i is then the index of a present field."
  [^ClassWriter cw c t n]
  (let [mv (method cw Opcodes/ACC_PRIVATE "field" "()Z")
        top (Label.) skip (Label.)]
    (.visitLabel mv top)
    (iter-load! mv c "i" "I") (.visitVarInsn mv Opcodes/ISTORE 1)
    (table-switch! mv n 1 (fn [j]
                            (iter-field! mv c t j) (static! mv t "ABSENT" OBJ-D)
                            (jump! mv Opcodes/IF_ACMPEQ skip)
                            (op! mv Opcodes/ICONST_1 Opcodes/IRETURN)))
    (op! mv Opcodes/ICONST_0 Opcodes/IRETURN)
    (.visitLabel mv skip)
    (aload! mv 0) (.visitVarInsn mv Opcodes/ILOAD 1) (op! mv Opcodes/ICONST_1 Opcodes/IADD)
    (.visitFieldInsn mv Opcodes/PUTFIELD c "i" "I")
    (jump! mv Opcodes/GOTO top)
    (end! mv)))

(defn- iter-rest-method!
  "private Iterator rest() of T$I, `c`: ext's iterator, made once."
  [^ClassWriter cw c]
  (let [IT-D "Ljava/util/Iterator;"
        mv (method cw Opcodes/ACC_PRIVATE "rest" (str "()" IT-D)) made (Label.)]
    (iter-load! mv c "it" IT-D) (jump! mv Opcodes/IFNONNULL made)
    (aload! mv 0) (iter-load! mv c "ext" IPM-D) (invoke! mv Iterable "iterator")
    (.visitFieldInsn mv Opcodes/PUTFIELD c "it" IT-D)
    (.visitLabel mv made)
    (iter-load! mv c "it" IT-D) (op! mv Opcodes/ARETURN) (end! mv)))

(defn- iter-has-next-method!
  "public boolean hasNext() of T$I, `c`: whether a present field or ext's iterator has more."
  [^ClassWriter cw c]
  (let [IT-D "Ljava/util/Iterator;"
        mv (method cw Opcodes/ACC_PUBLIC "hasNext" "()Z") rest (Label.)]
    (aload! mv 0) (.visitMethodInsn mv Opcodes/INVOKESPECIAL c "field" "()Z" false)
    (jump! mv Opcodes/IFEQ rest)
    (op! mv Opcodes/ICONST_1 Opcodes/IRETURN)
    (.visitLabel mv rest)
    (aload! mv 0) (.visitMethodInsn mv Opcodes/INVOKESPECIAL c "rest" (str "()" IT-D) false)
    (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Iterator" "hasNext" "()Z" true)
    (op! mv Opcodes/IRETURN) (end! mv)))

(defn- iter-next-method!
  "public Object next() of T$I, `c`, over the n fields of T, `t`: the entry of the field at
  i, or its key or value as `mode` asks, and i moves on; past the fields, the same of the
  next entry of ext's iterator."
  [^ClassWriter cw c t n]
  (let [IT-D "Ljava/util/Iterator;"
        mv (method cw Opcodes/ACC_PUBLIC "next" (str "()" OBJ-D)) rest (Label.) entry (Label.) key (Label.)]
    (aload! mv 0) (.visitMethodInsn mv Opcodes/INVOKESPECIAL c "field" "()Z" false)
    (jump! mv Opcodes/IFEQ rest)
    (iter-load! mv c "i" "I") (.visitVarInsn mv Opcodes/ISTORE 1)
    (aload! mv 0) (.visitVarInsn mv Opcodes/ILOAD 1) (op! mv Opcodes/ICONST_1 Opcodes/IADD)
    (.visitFieldInsn mv Opcodes/PUTFIELD c "i" "I")
    (table-switch! mv n 1 (fn [j]
                            (static! mv c (str "K" j) OBJ-D) (astore! mv 2)
                            (iter-field! mv c t j) (astore! mv 3)
                            (jump! mv Opcodes/GOTO entry)))
    (.visitLabel mv rest)
    (aload! mv 0) (.visitMethodInsn mv Opcodes/INVOKESPECIAL c "rest" (str "()" IT-D) false)
    (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Iterator" "next" (str "()" OBJ-D) true)
    (astore! mv 4)
    (iter-load! mv c "mode" "I") (jump! mv Opcodes/IFNE key)
    (aload! mv 4) (op! mv Opcodes/ARETURN)
    (.visitLabel mv key)
    (aload! mv 4) (cast! mv java.util.Map$Entry)
    (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Map$Entry" "getKey" (str "()" OBJ-D) true) (astore! mv 2)
    (aload! mv 4) (cast! mv java.util.Map$Entry)
    (.visitMethodInsn mv Opcodes/INVOKEINTERFACE "java/util/Map$Entry" "getValue" (str "()" OBJ-D) true) (astore! mv 3)
    (.visitLabel mv entry)
    (let [not-entry (Label.) not-key (Label.)]
      (iter-load! mv c "mode" "I") (jump! mv Opcodes/IFNE not-entry)
      (aload! mv 2) (aload! mv 3)
      (map-entry! mv)
      (op! mv Opcodes/ARETURN)
      (.visitLabel mv not-entry)
      (iter-load! mv c "mode" "I") (op! mv Opcodes/ICONST_1) (jump! mv Opcodes/IF_ICMPNE not-key)
      (aload! mv 2) (op! mv Opcodes/ARETURN)
      (.visitLabel mv not-key)
      (aload! mv 3) (op! mv Opcodes/ARETURN))
    (end! mv)))

(defn iter-bytes
  "T$I's bytes: an Iterator over a T's present fields, in the order of the keys, then over
  its ext, answering entries (mode 0), keys (1) or values (2). It reads the fields of the T
  it is given, so no seq or map is built. It holds its own K<i>, since T's are private."
  [t ks]
  (let [cw   (ClassWriter. ClassWriter/COMPUTE_FRAMES)
        c    (iter-name t)
        n    (count ks)
        pub  Opcodes/ACC_PUBLIC
        fin  Opcodes/ACC_FINAL]
    (.visit cw Opcodes/V1_8 (bit-or pub fin Opcodes/ACC_SUPER) c nil OBJ (into-array String ["java/util/Iterator"]))
    (iter-fields! cw t n)
    (iter-static-initializer! cw c ks)
    (iter-constructor! cw c t)
    (iter-field-method! cw c t n)
    (iter-rest-method! cw c)
    (iter-has-next-method! cw c)
    (iter-next-method! cw c t n)
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
                          (map-entry! mv)
                          (aload! mv 1)
                          (.visitMethodInsn mv Opcodes/INVOKESPECIAL "clojure/lang/Cons" "<init>"
                                            (str "(" OBJ-D "Lclojure/lang/ISeq;)V") false)
                          (astore! mv 1))))
      (aload! mv 1) (op! mv ret) (end! mv))
    (doseq [[nm mode] [["iterator" 0] ["keyIterator" 1] ["valIterator" 2]]]
      (doto (method cw pub nm "()Ljava/util/Iterator;")
        (.visitTypeInsn Opcodes/NEW (iter-name t)) (op! Opcodes/DUP)
        (aload! 0) (load-ext t) (.visitInsn (int (+ Opcodes/ICONST_0 mode)))
        (.visitMethodInsn Opcodes/INVOKESPECIAL (iter-name t) "<init>" (str "(L" t ";" IPM-D "I)V") false)
        (op! ret) (end!)))))

(defn- folds-of
  "The [method interface] pairs of reduce and kvreduce that T implements itself: both, less
  any that a method of `plan` forwards, by the same name and parameters."
  [plan]
  (let [listed? (fn [nm] (some #(and (= nm (:name %)) (= [clojure.lang.IFn Object] (vec (:params %)))) plan))]
    (remove (comp listed? first) [["reduce" clojure.lang.IReduceInit] ["kvreduce" clojure.lang.IKVReduce]])))

(defn- fold-reduced!
  "if (RT.isReduced(local 2)) return local 2, or with `deref?` its deref."
  [^MethodVisitor mv deref?]
  (let [go-on (Label.)]
    (aload! mv 2)
    (.visitMethodInsn mv Opcodes/INVOKESTATIC (iname RT) "isReduced" (str "(" OBJ-D ")Z") false)
    (jump! mv Opcodes/IFEQ go-on)
    (aload! mv 2)
    (when deref? (cast! mv clojure.lang.IDeref) (invoke! mv clojure.lang.IDeref "deref"))
    (op! mv Opcodes/ARETURN)
    (.visitLabel mv go-on)))

(defn- fold-step!
  "local 2 = f.invoke(local 2, (push!)), f in local 1, then fold-reduced!. `push!` pushes an
  entry, or with `kv?` a key and a value."
  [^MethodVisitor mv kv? deref? push!]
  (aload! mv 1) (aload! mv 2) (push!)
  (if kv?
    (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke" (str "(" OBJ-D OBJ-D OBJ-D ")" OBJ-D) true)
    (.visitMethodInsn mv Opcodes/INVOKEINTERFACE IFN "invoke" (str "(" OBJ-D OBJ-D ")" OBJ-D) true))
  (astore! mv 2)
  (fold-reduced! mv deref?))

(defn- fold-fields!
  "fold-step! with each present field of T, `t`, whose key's index is in [lo hi), in order."
  [^MethodVisitor mv t kv? deref? lo hi]
  (doseq [i (range lo hi)]
    (unless-absent! mv t i
                    #(fold-step! mv kv? deref?
                                 (fn []
                                   (load-key mv t i) (load-field mv t i)
                                   (when-not kv?
                                     (map-entry! mv)))))))

(defn- fold-methods!
  "Emits each method of `folds`: reduce(f, init) calls f with each entry, kvreduce(f, init)
  with each key and value, over the present fields in the order of the keys and then ext's
  entries; at a reduced accumulation it stops and returns its deref. A wide T walks its
  fields in chunks, each a private method reduce$c or kvreduce$c(f, acc) that answers the
  accumulation, a reduced one as it is."
  [^ClassWriter cw t n folds]
  (let [pub Opcodes/ACC_PUBLIC ret Opcodes/ARETURN
        desc (str "(" IFN-D OBJ-D ")" OBJ-D)]
    (doseq [[nm _] folds]
      (let [kv? (= nm "kvreduce")
            mv (method cw pub nm desc)
            top (Label.) end (Label.)]
        (if (wide? n)
          (doseq [[c [lo hi]] (map-indexed vector (chunks n))
                  :let [part (str nm "$" c)
                        cm (method cw Opcodes/ACC_PRIVATE part desc)]]
            (fold-fields! cm t kv? false lo hi)
            (aload! cm 2) (op! cm ret) (end! cm)
            (aload! mv 0) (aload! mv 1) (aload! mv 2)
            (.visitMethodInsn mv Opcodes/INVOKESPECIAL t part desc false)
            (astore! mv 2)
            (fold-reduced! mv true))
          (fold-fields! mv t kv? true 0 n))
        (load-ext mv t) (invoke! mv clojure.lang.Seqable "seq") (astore! mv 3)
        (.visitLabel mv top)
        (aload! mv 3) (jump! mv Opcodes/IFNULL end)
        (aload! mv 3) (invoke! mv clojure.lang.ISeq "first") (astore! mv 4)
        (fold-step! mv kv? true
                    (fn []
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
  "T's equiv and equals: against an instance of T, field by field and then ext, with no seq;
  against anything else, APersistentMap's."
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

(defn- class-header!
  "Declares T: public and final, extending APersistentMap and implementing IObj,
  IEditableCollection, IMapIterable and Proven; Built where unsealed; IKeywordLookup where
  `n`, the count of declared keys, is positive; and the interfaces of `folds` and `ifaces`."
  [^ClassWriter cw t n ifaces folds unsealed?]
  (let [pub Opcodes/ACC_PUBLIC fin Opcodes/ACC_FINAL super (iname clojure.lang.APersistentMap)]
    (.visit cw Opcodes/V1_8 (bit-or pub fin Opcodes/ACC_SUPER) t nil super
            (into-array String (distinct
                                (concat [(iname clojure.lang.IObj) (iname clojure.lang.IEditableCollection)
                                         (iname clojure.lang.IMapIterable)
                                         (iname recognitum.proof.Proven)]
                                        (when unsealed? [(iname recognitum.proof.Built)])
                                        (when (pos? n) [(iname clojure.lang.IKeywordLookup)])
                                        (map (comp iname second) folds)
                                        (map iname ifaces)))))))

(defn- field-declarations!
  "Declares T's fields:

  - static: KEY and ABSENT; `claimed`, the flag of claim; FNS and REMOVED, which claim sets;
    WRITES, CHG and GATE, which install sets;
  - per value: ext, _meta, cnt and, where unsealed, mem;
  - per declared key i: the static K<i>, the static G<i>, which install sets, and the field
    f<i>."
  [^ClassWriter cw n unsealed?]
  (let [priv Opcodes/ACC_PRIVATE stat Opcodes/ACC_STATIC fin Opcodes/ACC_FINAL]
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
                               (when unsealed? [[(bit-or priv fin) "mem" OBJ-D]])
                               (for [i (range n)] [(bit-or priv stat fin) (str "K" i) OBJ-D])
                               (for [i (range n)] [(bit-or priv stat Opcodes/ACC_VOLATILE) (str "G" i) IFN-D])
                               (for [i (range n)] [fin (str "f" i) OBJ-D]))]
      (.visitEnd (.visitField cw (int acc) nm d nil nil)))))

(defn- static-initializer!
  "static { KEY = new Object(); ABSENT = new Object(); K<i> = Keyword.intern(ns, name); }"
  [^ClassWriter cw t ks]
  (let [mv (method cw Opcodes/ACC_STATIC "<clinit>" "()V")]
    (doseq [f ["KEY" "ABSENT"]]
      (.visitTypeInsn mv Opcodes/NEW OBJ)
      (op! mv Opcodes/DUP)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL OBJ "<init>" "()V" false)
      (.visitFieldInsn mv Opcodes/PUTSTATIC t f OBJ-D))
    (intern-keys! mv t ks)
    (op! mv Opcodes/RETURN)
    (end! mv)))

(defn- static-claim!
  "public static synchronized Object claim(Object[] fns, Object removed): the first call sets
  FNS and REMOVED, the strategy's marker for a removed key, and returns KEY; a later call
  throws SecurityException."
  [^ClassWriter cw t]
  (let [mv (method cw (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC Opcodes/ACC_SYNCHRONIZED) "claim" (str "([Ljava/lang/Object;" OBJ-D ")" OBJ-D))
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
    (op! mv Opcodes/ARETURN)
    (end! mv)))

(defn- static-install!
  "public static synchronized void install(Object key, Object writes, Object gate, Object[]
  guards, Object changes). Throws SecurityException unless `key` is KEY, and where WRITES is
  already set. Sets:

  - WRITES to `writes`, which assoc, without, assocEx, cons and asTransient call;
  - GATE to `gate`, which gate() returns;
  - where `guards` is not null, each G<i> to guards[i], the guard of the i-th declared key,
    or null for none;
  - where `changes` is not null, CHG to `changes`, which assoc, without, cons and
    asTransient call in place of WRITES."
  [^ClassWriter cw t n]
  (let [mv (method cw (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC Opcodes/ACC_SYNCHRONIZED) "install" (str "(" OBJ-D OBJ-D OBJ-D "[" OBJ-D OBJ-D ")V"))
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
    (end! mv)))

(defn- static-gate!
  "public static IFn gate() { return GATE; }"
  [^ClassWriter cw t]
  (doto (method cw (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC) "gate" (str "()" IFN-D))
    (static! t "GATE" IFN-D)
    (op! Opcodes/ARETURN) (end!)))

(defn- ext-of-data!
  "Pushes this and then ext = (data.count() == present) ? {} : data without each of the n
  declared keys. Data is in local `m`; `present!` stores present, the count of present
  fields, in int local `c`. The fields must already be set from data."
  [^MethodVisitor mv t n m c present!]
  (let [some-other (Label.) done (Label.)]
    (present! mv c)
    (aload! mv m)
    (invoke! mv clojure.lang.Counted "count")
    (.visitVarInsn mv Opcodes/ILOAD c)
    (jump! mv Opcodes/IF_ICMPNE some-other)
    (aload! mv 0)
    (static! mv "clojure/lang/PersistentArrayMap" "EMPTY" "Lclojure/lang/PersistentArrayMap;")
    (cast! mv clojure.lang.IPersistentMap)
    (jump! mv Opcodes/GOTO done)
    (.visitLabel mv some-other)
    (aload! mv 0)
    (aload! mv m)
    (dotimes [i n]
      (load-key mv t i)
      (invoke! mv clojure.lang.IPersistentMap "without" Object))
    (.visitLabel mv done)))

(defn- meta-of-data!
  "_meta = data instanceof IMeta ? ((IMeta) data).meta() : null, data in local 2."
  [^MethodVisitor mv t]
  (let [no-meta (Label.)]
    (aload! mv 2)
    (.visitTypeInsn mv Opcodes/INSTANCEOF (iname clojure.lang.IMeta))
    (jump! mv Opcodes/IFEQ no-meta)
    (aload! mv 0)
    (aload! mv 2)
    (cast! mv clojure.lang.IMeta)
    (invoke! mv clojure.lang.IMeta "meta")
    (.visitFieldInsn mv Opcodes/PUTFIELD t "_meta" IPM-D)
    (.visitLabel mv no-meta)))

(defn- data-constructor!
  "public T(Object key, Object data); of an unsealed T, T(Object key, Object data, Object
  mem). Before super() runs, it throws SecurityException unless `key` is KEY, and
  IllegalArgumentException unless `data` is an IPersistentMap. Then:

  - each field f<i> takes data's entry under K<i>, or ABSENT;
  - ext takes the other entries;
  - cnt takes data's count, and _meta data's meta;
  - of an unsealed T, mem takes `mem`.

  `present!` stores the count of present fields in an int local."
  [^ClassWriter cw t n unsealed? instead present!]
  (let [mv (method cw Opcodes/ACC_PUBLIC "<init>" (str "(" OBJ-D OBJ-D (when unsealed? OBJ-D) ")V"))
        ok (Label.)
        m  (if unsealed? 4 3)
        c  (inc m)]
    (require-key! mv t 1 (no-key-message t instead))
    (aload! mv 2)
    (.visitTypeInsn mv Opcodes/INSTANCEOF IPM)
    (jump! mv Opcodes/IFNE ok)
    (throw! mv IllegalArgumentException "data must be a persistent map")
    (.visitLabel mv ok)
    (super-init! mv)
    (aload! mv 2)
    (cast! mv clojure.lang.IPersistentMap)
    (astore! mv m)
    (when unsealed?
      (aload! mv 0) (aload! mv 3) (.visitFieldInsn mv Opcodes/PUTFIELD t "mem" OBJ-D))
    (dotimes [i n]
      (aload! mv 0)
      (aload! mv m)
      (load-key mv t i)
      (load-absent mv t)
      (invoke! mv clojure.lang.ILookup "valAt" Object Object)
      (.visitFieldInsn mv Opcodes/PUTFIELD t (str "f" i) OBJ-D))
    (if (zero? n)
      (do (aload! mv 0) (aload! mv m))
      (ext-of-data! mv t n m c present!))
    (.visitFieldInsn mv Opcodes/PUTFIELD t "ext" IPM-D)
    (aload! mv 0) (aload! mv m) (invoke! mv clojure.lang.Counted "count")
    (.visitFieldInsn mv Opcodes/PUTFIELD t "cnt" "I")
    (meta-of-data! mv t)
    (op! mv Opcodes/RETURN)
    (end! mv)))

(defn- copy-fields!
  "this.f = src.f, src a T in local 1, for each [f d] of `fields`, a field's name and descriptor."
  [^MethodVisitor mv t fields]
  (doseq [[f d] fields]
    (aload! mv 0) (aload! mv 1)
    (.visitFieldInsn mv Opcodes/GETFIELD t f d)
    (.visitFieldInsn mv Opcodes/PUTFIELD t f d)))

(defn- meta-constructor!
  "private T(T src, IPersistentMap meta): src's entries and memory, new meta."
  [^ClassWriter cw t n unsealed?]
  (let [mv (method cw Opcodes/ACC_PRIVATE "<init>" (str "(L" t ";" IPM-D ")V"))]
    (super-init! mv)
    (copy-fields! mv t (concat [["ext" IPM-D] ["cnt" "I"]] (when unsealed? [["mem" OBJ-D]])
                               (for [i (range n)] [(str "f" i) OBJ-D])))
    (aload! mv 0)
    (aload! mv 2)
    (.visitFieldInsn mv Opcodes/PUTFIELD t "_meta" IPM-D)
    (op! mv Opcodes/RETURN)
    (end! mv)))

(defn- flat-constructor!
  "private T(IPersistentMap meta, IPersistentMap ext, int cnt, Object f0, ...): the fields as
  given. Only assoc$i calls it, where a guard returned; an unsealed T, or a T of no keys, has
  none."
  [^ClassWriter cw t n unsealed?]
  (when (and (pos? n) (not unsealed?))
    (let [mv (method cw Opcodes/ACC_PRIVATE "<init>" (flat-desc n))]
      (super-init! mv)
      (aload! mv 0) (aload! mv 1) (.visitFieldInsn mv Opcodes/PUTFIELD t "_meta" IPM-D)
      (aload! mv 0) (aload! mv 2) (.visitFieldInsn mv Opcodes/PUTFIELD t "ext" IPM-D)
      (aload! mv 0) (.visitVarInsn mv Opcodes/ILOAD 3) (.visitFieldInsn mv Opcodes/PUTFIELD t "cnt" "I")
      (dotimes [j n]
        (aload! mv 0) (aload! mv (+ 4 j)) (.visitFieldInsn mv Opcodes/PUTFIELD t (str "f" j) OBJ-D))
      (op! mv Opcodes/RETURN)
      (end! mv))))

(defn- index-method!
  "private static int index$(Object k): the index of declared key k, else -1."
  [^ClassWriter cw t ks]
  (let [mv (method cw (bit-or Opcodes/ACC_PRIVATE Opcodes/ACC_STATIC) "index$" (str "(" OBJ-D ")I"))]
    (by-key! mv t ks 0 (fn [i] (push-int! mv i) (op! mv Opcodes/IRETURN)))
    (op! mv Opcodes/ICONST_M1 Opcodes/IRETURN)
    (end! mv)))

(defn- wide-methods!
  "Of a wide T: private Object field$(int i), the field of the i-th declared key, throwing
  IndexOutOfBoundsException for an i outside [0 n); private int present$(), how many fields
  are present. `count!` stores that count in an int local. Of any other T, nothing."
  [^ClassWriter cw t n count!]
  (when (wide? n)
    (let [mv (method cw Opcodes/ACC_PRIVATE "field$" (str "(I)" OBJ-D))
          labels (vec (repeatedly n #(Label.))) dflt (Label.)]
      (.visitVarInsn mv Opcodes/ILOAD 1)
      (.visitTableSwitchInsn mv 0 (dec n) dflt (into-array Label labels))
      (dotimes [i n]
        (.visitLabel mv (labels i))
        (load-field mv t i) (op! mv Opcodes/ARETURN))
      (.visitLabel mv dflt)
      (throw! mv IndexOutOfBoundsException "no declared key has this index")
      (end! mv))
    (doto (method cw Opcodes/ACC_PRIVATE "present$" "()I")
      (count! 1)
      (.visitVarInsn Opcodes/ILOAD 1) (op! Opcodes/IRETURN)
      (end!))))

(defn- delta-method!
  "private static int delta$(Object was, Object now): how a field's change moves the count:
  1 where `was` is ABSENT and `now` is not, -1 where `now` is ABSENT and `was` is not, else 0."
  [^ClassWriter cw t]
  (let [mv (method cw (bit-or Opcodes/ACC_PRIVATE Opcodes/ACC_STATIC) "delta$" (str "(" OBJ-D OBJ-D ")I"))
        present (Label.) same (Label.)]
    (aload! mv 0) (load-absent mv t) (jump! mv Opcodes/IF_ACMPNE present)
    (aload! mv 1) (load-absent mv t) (jump! mv Opcodes/IF_ACMPEQ same)
    (op! mv Opcodes/ICONST_1 Opcodes/IRETURN)
    (.visitLabel mv present)
    (aload! mv 1) (load-absent mv t) (jump! mv Opcodes/IF_ACMPNE same)
    (op! mv Opcodes/ICONST_M1 Opcodes/IRETURN)
    (.visitLabel mv same)
    (op! mv Opcodes/ICONST_0 Opcodes/IRETURN)
    (end! mv)))

(defn- put-declared!
  "Emits, inside the change constructor, the code that stores one pair into its key's field
  where T, of n declared keys, declares that key. The locals:

  - int local 9: j, the key's index, or -1 for a key T does not declare;
  - local 6: v, the pair's value;
  - int local 7: the count less ext's count;
  - local 8: scratch.

  Where j is a declared key's index, f<j> takes v, or ABSENT where v is REMOVED, local 7
  moves by delta$, and the code jumps to `nxt`. Where j is -1, the code falls through."
  [^MethodVisitor mv t n nxt]
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
      ;; local 7 += delta$(f<j>, local 8): per key where T is not wide, else once, through field$
      (let [delta! (fn [load!]
                     (load!) (aload! mv 8)
                     (.visitMethodInsn mv Opcodes/INVOKESTATIC t "delta$" (str "(" OBJ-D OBJ-D ")I") false)
                     (.visitVarInsn mv Opcodes/ILOAD 7) (op! mv Opcodes/IADD) (.visitVarInsn mv Opcodes/ISTORE 7))]
        (when (wide? n) (delta! #(load-field-at mv t 9)))
        (.visitVarInsn mv Opcodes/ILOAD 9)
        (.visitTableSwitchInsn mv 0 (dec n) undeclared (into-array Label labels))
        (dotimes [i n]
          (.visitLabel mv (labels i))
          (when-not (wide? n) (delta! #(load-field mv t i)))
          (aload! mv 0) (aload! mv 8)
          (.visitFieldInsn mv Opcodes/PUTFIELD t (str "f" i) OBJ-D)
          (jump! mv Opcodes/GOTO nxt)))
      (.visitLabel mv undeclared))))

(defn- change-constructor!
  "private T(T src, Object[] ch): src's entries and meta with ch's pairs k, v applied in order,
  v REMOVED for a removal. Only the code [[change!]] emits calls it, with the pairs CHG
  answered. Of an unsealed T, ch's last element is the new value's memory, after the pairs."
  [^ClassWriter cw t n unsealed?]
  (let [mv (method cw Opcodes/ACC_PRIVATE "<init>" (str "(L" t ";[" OBJ-D ")V"))
        top (Label.) nxt (Label.) done (Label.) put-ext (Label.)]
    (super-init! mv)
    ;; of an unsealed T: int local 10 = ch.length - 1, where the pairs end; mem = ch[local 10]
    (when unsealed?
      (aload! mv 2) (op! mv Opcodes/ARRAYLENGTH Opcodes/ICONST_1 Opcodes/ISUB)
      (.visitVarInsn mv Opcodes/ISTORE 10)
      (aload! mv 0) (aload! mv 2) (.visitVarInsn mv Opcodes/ILOAD 10) (op! mv Opcodes/AALOAD)
      (.visitFieldInsn mv Opcodes/PUTFIELD t "mem" OBJ-D))
    (copy-fields! mv t (cons ["_meta" IPM-D] (for [i (range n)] [(str "f" i) OBJ-D])))
    (aload! mv 1) (.visitFieldInsn mv Opcodes/GETFIELD t "ext" IPM-D) (astore! mv 3)
    ;; int local 7: src's count less ext's count, which put-declared! moves as fields change
    (aload! mv 1) (.visitFieldInsn mv Opcodes/GETFIELD t "cnt" "I")
    (aload! mv 3) (invoke! mv clojure.lang.Counted "count") (op! mv Opcodes/ISUB)
    (.visitVarInsn mv Opcodes/ISTORE 7)
    (op! mv Opcodes/ICONST_0) (.visitVarInsn mv Opcodes/ISTORE 4)
    (.visitLabel mv top)
    (.visitVarInsn mv Opcodes/ILOAD 4)
    (if unsealed?
      (.visitVarInsn mv Opcodes/ILOAD 10)
      (do (aload! mv 2) (op! mv Opcodes/ARRAYLENGTH)))
    (jump! mv Opcodes/IF_ICMPGE done)
    (aload! mv 2) (.visitVarInsn mv Opcodes/ILOAD 4) (op! mv Opcodes/AALOAD) (astore! mv 5)
    (aload! mv 2) (.visitVarInsn mv Opcodes/ILOAD 4) (op! mv Opcodes/ICONST_1 Opcodes/IADD Opcodes/AALOAD) (astore! mv 6)
    ;; j = index$(k); put-declared! stores a declared key's pair through a switch on j, so
    ;; this method grows by a few instructions per key; an undeclared key's pair goes to ext
    (aload! mv 5)
    (.visitMethodInsn mv Opcodes/INVOKESTATIC t "index$" (str "(" OBJ-D ")I") false)
    (.visitVarInsn mv Opcodes/ISTORE 9)
    (put-declared! mv t n nxt)
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
    (end! mv)))

(defn- with-ext-method!
  "private IPersistentMap withExt(IPersistentMap e): a plain map of the present fields'
  entries and e's entries; e itself where T declares no keys. `e` must hold no declared key.
  `present!` stores the count of present fields in an int local; `fill!` stores the present
  fields' keys and values in an array."
  [^ClassWriter cw t n present! fill!]
  (let [mv (method cw Opcodes/ACC_PRIVATE "withExt" (str "(" IPM-D ")" IPM-D))]
    (if (zero? n)
      (do (aload! mv 1) (op! mv Opcodes/ARETURN))
      (let [more (Label.)]
        (present! mv 2)
        (.visitVarInsn mv Opcodes/ILOAD 2)
        (op! mv Opcodes/ICONST_1 Opcodes/ISHL)
        (.visitTypeInsn mv Opcodes/ANEWARRAY OBJ)
        (astore! mv 3)
        (op! mv Opcodes/ICONST_0)
        (.visitVarInsn mv Opcodes/ISTORE 4)
        (if (wide? n)
          (doseq [[c [lo hi]] (map-indexed vector (chunks n))
                  :let [part (str "fill$" c) desc (str "([" OBJ-D "I)I")
                        cm (method cw Opcodes/ACC_PRIVATE part desc)]]
            (fill! cm 1 2 lo hi)
            (.visitVarInsn cm Opcodes/ILOAD 2) (op! cm Opcodes/IRETURN) (end! cm)
            (aload! mv 0) (aload! mv 3) (.visitVarInsn mv Opcodes/ILOAD 4)
            (.visitMethodInsn mv Opcodes/INVOKESPECIAL t part desc false)
            (.visitVarInsn mv Opcodes/ISTORE 4))
          (fill! mv 3 4 0 n))
        (aload! mv 3)
        (.visitMethodInsn mv Opcodes/INVOKESTATIC (iname RT) "mapUniqueKeys" (str "([Ljava/lang/Object;)" IPM-D) false)
        (astore! mv 5)
        (aload! mv 1)
        (invoke! mv clojure.lang.Counted "count")
        (jump! mv Opcodes/IFNE more)
        (aload! mv 5)
        (op! mv Opcodes/ARETURN)
        (.visitLabel mv more)
        (aload! mv 5)
        (aload! mv 1)
        (invoke! mv clojure.lang.IPersistentCollection "cons" Object)
        (cast! mv clojure.lang.IPersistentMap)
        (op! mv Opcodes/ARETURN)))
    (end! mv)))

(defn- plain-method!
  "private Object plain(Object r): r with this T's _meta where _meta is not null; else r."
  [^ClassWriter cw t]
  (let [mv (method cw Opcodes/ACC_PRIVATE "plain" (str "(" OBJ-D ")" OBJ-D))
        some-meta (Label.)]
    (aload! mv 0)
    (.visitFieldInsn mv Opcodes/GETFIELD t "_meta" IPM-D)
    (jump! mv Opcodes/IFNONNULL some-meta)
    (aload! mv 1)
    (op! mv Opcodes/ARETURN)
    (.visitLabel mv some-meta)
    (aload! mv 1)
    (cast! mv clojure.lang.IObj)
    (aload! mv 0)
    (.visitFieldInsn mv Opcodes/GETFIELD t "_meta" IPM-D)
    (invoke! mv clojure.lang.IObj "withMeta" clojure.lang.IPersistentMap)
    (op! mv Opcodes/ARETURN)
    (end! mv)))

(defn- read-methods!
  "T's reads, valAt of one and two arguments, containsKey and entryAt: a declared key reads
  its field, ABSENT read as not found; any other key reads ext."
  [^ClassWriter cw t ks]
  (let [pub Opcodes/ACC_PUBLIC ret Opcodes/ARETURN]
    (let [mv (method cw pub "valAt" (mdesc clojure.lang.ILookup "valAt" Object))]
      (by-field! mv t ks 1 3 (fn [load!]
                               (let [absent (Label.)]
                                 (load!) (astore! mv 2) (aload! mv 2) (load-absent mv t)
                                 (jump! mv Opcodes/IF_ACMPEQ absent)
                                 (aload! mv 2) (op! mv ret)
                                 (.visitLabel mv absent)
                                 (op! mv Opcodes/ACONST_NULL ret))))
      (load-ext mv t) (aload! mv 1) (invoke! mv clojure.lang.ILookup "valAt" Object) (op! mv ret)
      (end! mv))
    (let [mv (method cw pub "valAt" (mdesc clojure.lang.ILookup "valAt" Object Object))]
      (by-field! mv t ks 1 4 (fn [load!]
                               (let [absent (Label.)]
                                 (load!) (astore! mv 3) (aload! mv 3) (load-absent mv t)
                                 (jump! mv Opcodes/IF_ACMPEQ absent)
                                 (aload! mv 3) (op! mv ret)
                                 (.visitLabel mv absent)
                                 (aload! mv 2) (op! mv ret))))
      (load-ext mv t) (aload! mv 1) (aload! mv 2) (invoke! mv clojure.lang.ILookup "valAt" Object Object) (op! mv ret)
      (end! mv))
    (let [mv (method cw pub "containsKey" (mdesc clojure.lang.Associative "containsKey" Object))]
      (by-field! mv t ks 1 2 (fn [load!]
                               (let [absent (Label.)]
                                 (load!) (load-absent mv t)
                                 (jump! mv Opcodes/IF_ACMPEQ absent)
                                 (op! mv Opcodes/ICONST_1 Opcodes/IRETURN)
                                 (.visitLabel mv absent)
                                 (op! mv Opcodes/ICONST_0 Opcodes/IRETURN))))
      (load-ext mv t) (aload! mv 1) (invoke! mv clojure.lang.Associative "containsKey" Object) (op! mv Opcodes/IRETURN)
      (end! mv))
    (let [mv (method cw pub "entryAt" (mdesc clojure.lang.Associative "entryAt" Object))]
      (by-field! mv t ks 1 2 (fn [load!]
                               (let [absent (Label.)]
                                 (load!) (load-absent mv t)
                                 (jump! mv Opcodes/IF_ACMPEQ absent)
                                 (aload! mv 1) (load!)
                                 (map-entry! mv)
                                 (op! mv ret)
                                 (.visitLabel mv absent)
                                 (op! mv Opcodes/ACONST_NULL ret))))
      (load-ext mv t) (aload! mv 1) (invoke! mv clojure.lang.Associative "entryAt" Object) (op! mv ret)
      (end! mv))))

(defn- count-method!
  "public int count() { return cnt; }"
  [^ClassWriter cw t]
  (let [mv (method cw Opcodes/ACC_PUBLIC "count" (mdesc clojure.lang.Counted "count"))]
    (aload! mv 0) (.visitFieldInsn mv Opcodes/GETFIELD t "cnt" "I")
    (op! mv Opcodes/IRETURN)
    (end! mv)))

(defn- lookup-thunk-method!
  "Where keys are declared, T implements IKeywordLookup: getLookupThunk(k) answers a new
  T$K<i> for the i-th declared key, else null, so a keyword's lookup of a declared key reads
  its field, as on a defrecord."
  [^ClassWriter cw t n ks]
  (when (pos? n)
    (let [mv (method cw Opcodes/ACC_PUBLIC "getLookupThunk" (mdesc clojure.lang.IKeywordLookup "getLookupThunk" clojure.lang.Keyword))]
      (by-key! mv t ks 1 (fn [i]
                           (.visitTypeInsn mv Opcodes/NEW (thunk-name t i))
                           (op! mv Opcodes/DUP)
                           (.visitMethodInsn mv Opcodes/INVOKESPECIAL (thunk-name t i) "<init>" "()V" false)
                           (op! mv Opcodes/ARETURN)))
      (op! mv Opcodes/ACONST_NULL Opcodes/ARETURN)
      (end! mv))))

(defn- field-assoc-methods!
  "Emits, per declared key i, private IPersistentMap assoc$i(Object v), the assoc of K<i>,
  in a method of its own so that assoc stays small whatever the count of keys. It returns:

  - this, where v is identical to f<i>;
  - where G<i> is set (never on an unsealed T), after G<i>.invoke(this, v) returns, a T
    from the flat constructor with f<i> = v;
  - where CHG is set, what [[change!]]'s code answers for K<i> and v;
  - else what [[write!]]'s code answers for the whole new map, K<i> and v."
  [^ClassWriter cw t n unsealed?]
  (dotimes [i n]
    (let [mv (method cw Opcodes/ACC_PRIVATE (str "assoc$" i) (str "(" OBJ-D ")" IPM-D))
          changed (Label.) unguarded (Label.) was (Label.)]
      (load-field mv t i) (aload! mv 1)
      (jump! mv Opcodes/IF_ACMPNE changed)
      (aload! mv 0) (op! mv Opcodes/ARETURN)
      (.visitLabel mv changed)
      (when-not unsealed?
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
        (op! mv Opcodes/ARETURN)
        (.visitLabel mv unguarded))
      (change! mv t 3 4 #(do (load-key mv t i) (aload! mv 1) 2))
      (load-entries mv t) (load-key mv t i) (aload! mv 1)
      (invoke! mv clojure.lang.IPersistentMap "assoc" Object Object)
      (astore! mv 5)
      (write! mv t 5 6 #(do (load-key mv t i) (aload! mv 1) 2))
      (end! mv))))

(defn- assoc-method!
  "public IPersistentMap assoc(Object k, Object v): for a declared key, its assoc$i. For any
  other key, through CHG where it is set, as [[change!]]'s code does; else this, where
  ext.assoc(k, v) is ext; else the whole new map, through [[write!]]'s code with k and v."
  [^ClassWriter cw t ks]
  (let [mv (method cw Opcodes/ACC_PUBLIC "assoc" (mdesc clojure.lang.IPersistentMap "assoc" Object Object))
        write (Label.)]
    (by-key! mv t ks 1 (fn [i]
                         (aload! mv 0) (aload! mv 2)
                         (.visitMethodInsn mv Opcodes/INVOKESPECIAL t (str "assoc$" i) (str "(" OBJ-D ")" IPM-D) false)
                         (op! mv Opcodes/ARETURN)))
    (change! mv t 6 7 #(do (aload! mv 1) (aload! mv 2) 2))
    (load-ext mv t) (aload! mv 1) (aload! mv 2)
    (invoke! mv clojure.lang.IPersistentMap "assoc" Object Object)
    (astore! mv 4)
    (return-this-if-ext! mv t 4)
    (aload! mv 0) (aload! mv 4)
    (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "withExt" (str "(" IPM-D ")" IPM-D) false)
    (astore! mv 3)
    (.visitLabel mv write)
    (write! mv t 3 5 #(do (aload! mv 1) (aload! mv 2) 2))
    (end! mv)))

(defn- without-method!
  "public IPersistentMap without(Object k): through CHG where it is set, with k and REMOVED,
  as [[change!]]'s code does; else this, where T lacks k; else the whole new map, through
  [[write!]]'s code with k and REMOVED."
  [^ClassWriter cw t ks]
  (let [mv (method cw Opcodes/ACC_PUBLIC "without" (mdesc clojure.lang.IPersistentMap "without" Object))
        write (Label.)]
    (change! mv t 5 6 #(do (aload! mv 1) (static! mv t "REMOVED" OBJ-D) 2))
    (by-field! mv t ks 1 7 (fn [load!]
                             (let [present (Label.)]
                               (load!) (load-absent mv t)
                               (jump! mv Opcodes/IF_ACMPNE present)
                               (aload! mv 0) (op! mv Opcodes/ARETURN)
                               (.visitLabel mv present)
                               (load-entries mv t) (aload! mv 1)
                               (invoke! mv clojure.lang.IPersistentMap "without" Object)
                               (astore! mv 2)
                               (jump! mv Opcodes/GOTO write))))
    (load-ext mv t) (aload! mv 1)
    (invoke! mv clojure.lang.IPersistentMap "without" Object)
    (astore! mv 3)
    (return-this-if-ext! mv t 3)
    (aload! mv 0) (aload! mv 3)
    (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "withExt" (str "(" IPM-D ")" IPM-D) false)
    (astore! mv 2)
    (.visitLabel mv write)
    (write! mv t 2 4 #(do (aload! mv 1) (static! mv t "REMOVED" OBJ-D) 2))
    (end! mv)))

(defn- assoc-ex-method!
  "public IPersistentMap assocEx(Object k, Object v): throws where T holds k. Else, of an
  unsealed T, its assoc(k, v); of any other T, the whole new map, through [[write!]]'s code
  with that map alone. CHG is not consulted."
  [^ClassWriter cw t unsealed?]
  (let [mv (method cw Opcodes/ACC_PUBLIC "assocEx" (mdesc clojure.lang.IPersistentMap "assocEx" Object Object))]
    (if unsealed?
      ;; if (containsKey(k)) throw ...; return assoc(k, v);
      (let [absent (Label.)]
        (aload! mv 0) (aload! mv 1)
        (.visitMethodInsn mv Opcodes/INVOKEVIRTUAL t "containsKey" (str "(" OBJ-D ")Z") false)
        (jump! mv Opcodes/IFEQ absent)
        (throw! mv RuntimeException "Key already present")
        (.visitLabel mv absent)
        (aload! mv 0) (aload! mv 1) (aload! mv 2)
        (.visitMethodInsn mv Opcodes/INVOKEVIRTUAL t "assoc" (str "(" OBJ-D OBJ-D ")" IPM-D) false)
        (op! mv Opcodes/ARETURN))
      (do (load-entries mv t) (aload! mv 1) (aload! mv 2)
          (invoke! mv clojure.lang.IPersistentMap "assocEx" Object Object)
          (astore! mv 3)
          (write! mv t 3 4 (constantly 0))))
    (end! mv)))

(defn- cons-method!
  "public IPersistentCollection cons(Object o): through CHG where it is set, with o, as
  [[change!]]'s code does; else this, where cons of o onto T's entries returns that same map;
  else the whole new map, through [[write!]]'s code with that map alone."
  [^ClassWriter cw t]
  (let [mv (method cw Opcodes/ACC_PUBLIC "cons" (mdesc clojure.lang.IPersistentMap "cons" Object))]
    (change! mv t 5 6 #(do (aload! mv 1) 1))
    (load-entries mv t) (astore! mv 2)
    (aload! mv 2) (aload! mv 1)
    (invoke! mv clojure.lang.IPersistentCollection "cons" Object)
    (astore! mv 3)
    (return-this-if-same! mv 3 2)
    (write! mv t 3 4 (constantly 0))
    (end! mv)))

(defn- as-transient-method!
  "public ITransientCollection asTransient() {
    c = CHG; if (c != null) return (ITransientCollection) c.invoke(this);
    w = WRITES; if (w == null) return ((IEditableCollection) withExt(ext)).asTransient();
    return (ITransientCollection) w.invoke(this); }"
  [^ClassWriter cw t]
  (let [ret Opcodes/ARETURN
        mv (method cw Opcodes/ACC_PUBLIC "asTransient" (mdesc clojure.lang.IEditableCollection "asTransient"))
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
    (end! mv)))

(defn- empty-method!
  "public IPersistentCollection empty() { throw new UnsupportedOperationException(...); }"
  [^ClassWriter cw]
  (let [mv (method cw Opcodes/ACC_PUBLIC "empty" (mdesc clojure.lang.IPersistentCollection "empty"))]
    (throw! mv UnsupportedOperationException "a value of a type has no empty value")
    (end! mv)))

(defn- meta-methods!
  "public IPersistentMap meta() { return _meta; }; withMeta(m): this where m is _meta, else a
  copy with m."
  [^ClassWriter cw t]
  (let [pub Opcodes/ACC_PUBLIC ret Opcodes/ARETURN]
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
      (end! mv))))

(defn- serialization-methods!
  "Serialization: writeReplace() writes T out as a plain map, with T's meta; readObject throws
  InvalidObjectException, so a stream naming T, which only a hand-made stream can be, reads
  nothing."
  [^ClassWriter cw t]
  (let [priv Opcodes/ACC_PRIVATE]
    (let [mv (method cw priv "writeReplace" (str "()" OBJ-D))]
      (aload! mv 0)
      (load-entries mv t)
      (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "plain" (str "(" OBJ-D ")" OBJ-D) false)
      (op! mv Opcodes/ARETURN)
      (end! mv))
    (doto (method cw priv "readObject" "(Ljava/io/ObjectInputStream;)V")
      (throw! java.io.InvalidObjectException "no key") (end!))))

(defn- create-method!
  "public static IPersistentMap create(IPersistentMap m) { return m; }: #T{..} reads as a plain
  map."
  [^ClassWriter cw]
  (doto (method cw (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC) "create" (str "(" IPM-D ")" IPM-D))
    (aload! 0)
    (op! Opcodes/ARETURN) (end!)))

(defn- memory-method!
  "Of an unsealed T: public Object memory$() { return mem; }"
  [^ClassWriter cw t unsealed?]
  (when unsealed?
    (doto (method cw Opcodes/ACC_PUBLIC "memory$" (str "()" OBJ-D))
      (aload! 0) (.visitFieldInsn Opcodes/GETFIELD t "mem" OBJ-D) (op! Opcodes/ARETURN) (end!))))

(defn value-class-bytes
  "T's bytes, from:

  - `t`, T's internal name;
  - `ifaces`, the listed interfaces, which T implements;
  - `plan`, the methods that T forwards, each to the function at its index in FNS;
  - `ks`, the declared keys, one field each;
  - `unsealed?`, true for an unsealed definition. Its T also holds a memory, `mem`, which its
    constructor takes after the data and memory$() answers, and which a change takes from
    the last element of what CHG answered; it has no guards, and its assocEx is its assoc
    where the key is absent;
  - `instead`, the words that close the message of T's constructor called without the access
    key, as [[no-key-message]] says."
  [t ifaces plan ks unsealed? instead]
  (let [cw    (ClassWriter. ClassWriter/COMPUTE_FRAMES)
        n     (count ks)
        folds (folds-of plan)
        ;; int local `slot` = the count of present fields
        count! (fn [^MethodVisitor mv slot]
                 (op! mv Opcodes/ICONST_0)
                 (.visitVarInsn mv Opcodes/ISTORE (int slot))
                 (dotimes [i n] (unless-absent! mv t i #(.visitIincInsn mv slot 1))))
        ;; the same, of a wide T by a call of present$()
        present! (fn [^MethodVisitor mv slot]
                   (if (wide? n)
                     (do (aload! mv 0)
                         (.visitMethodInsn mv Opcodes/INVOKESPECIAL t "present$" "()I" false)
                         (.visitVarInsn mv Opcodes/ISTORE (int slot)))
                     (count! mv slot)))
        ;; for each present field f<i>, i in [lo hi): local[a][p] = K<i>, local[a][p + 1] = f<i>, p += 2
        fill! (fn [^MethodVisitor mv a p lo hi]
                (doseq [i (range lo hi)]
                  (unless-absent! mv t i
                                  (fn []
                                    (aload! mv a) (.visitVarInsn mv Opcodes/ILOAD (int p)) (load-key mv t i) (op! mv Opcodes/AASTORE)
                                    (aload! mv a) (.visitVarInsn mv Opcodes/ILOAD (int p)) (op! mv Opcodes/ICONST_1 Opcodes/IADD)
                                    (load-field mv t i) (op! mv Opcodes/AASTORE)
                                    (.visitIincInsn mv p 2)))))]
    (class-header! cw t n ifaces folds unsealed?)
    (field-declarations! cw n unsealed?)
    (static-initializer! cw t ks)
    (static-claim! cw t)
    (static-install! cw t n)
    (static-gate! cw t)
    (data-constructor! cw t n unsealed? instead present!)
    (meta-constructor! cw t n unsealed?)
    (flat-constructor! cw t n unsealed?)
    (index-method! cw t ks)
    (wide-methods! cw t n count!)
    (delta-method! cw t)
    (change-constructor! cw t n unsealed?)
    (with-ext-method! cw t n present! fill!)
    (plain-method! cw t)
    (read-methods! cw t ks)
    (count-method! cw t)
    (lookup-thunk-method! cw t n ks)
    (walk-methods! cw t n)
    (fold-methods! cw t n folds)
    (equality-methods! cw t n)
    ;; the changes: this where nothing changes; else, for an assoc of a declared key whose
    ;; G<i> is set, G<i>.invoke(this, v), which returns or throws, then a T from the flat
    ;; constructor; else, where CHG is set, a T from the pairs CHG answers; else the whole new
    ;; map, through WRITES where it is set (with the key and value of an assoc, or the key and
    ;; REMOVED of a without), else as a plain map
    (field-assoc-methods! cw t n unsealed?)
    (assoc-method! cw t ks)
    (without-method! cw t ks)
    (assoc-ex-method! cw t unsealed?)
    (cons-method! cw t)
    (as-transient-method! cw t)
    (empty-method! cw)
    (meta-methods! cw t)
    (serialization-methods! cw t)
    (create-method! cw)
    (memory-method! cw t unsealed?)
    ;; the listed interfaces' methods, and toString where given
    (doseq [[i m] (map-indexed vector plan)] (forwarder! cw t i m))
    (.visitEnd cw)
    (.toByteArray cw)))

(defn draft-class-bytes
  "T$Draft's bytes, `d` its internal name and `t` T's. A draft holds a concurrent set of
  marked checks:

  - accept(key, check), of BiConsumer, marks `check`, and throws SecurityException unless
    `key` is T.KEY;
  - test(check), of Predicate, answers whether `check` is marked;
  - the static gate() returns T.gate()."
  [d t]
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
