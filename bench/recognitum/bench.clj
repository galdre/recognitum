(ns recognitum.bench
  "A hand-rolled `defrecord` with the same validation against a `defproven` type, sharing one
  set of field predicates, and the rows that time one against the other. The invariant
  checks are written twice: the hand-rolled side reads its fields out of a map, the
  library's are given the fields they name. No row fetches: a fetch would dominate every row.

  [[run]] prints the table.

    clojure -M:bench -e \"(require 'recognitum.bench)(recognitum.bench/run)\""
  (:require
   [clojure.edn]
   [clojure.string :as str]
   [recognitum.core :as rec]))

;;; ------------------------------------------------- the checks, shared by both sides

(defn non-blank-string? [x] (and (string? x) (not (str/blank? x))))
(defn crew-set?        [x] (and (set? x) (seq x) (every? keyword? x)))
(defn non-neg-int?     [x] (and (int? x) (not (neg? x))))
(defn cuts-map?        [x] (and (map? x) (every? keyword? (keys x)) (every? non-neg-int? (vals x))))

(defn cuts-add-up? [h] (= (:take h) (reduce + 0 (vals (:cuts h)))))
(defn only-crew?   [h] (every? (:crew h) (keys (:cuts h))))

(def field-preds {:name non-blank-string? :crew crew-set? :take non-neg-int? :cuts cuts-map?})

(def invariant-index
  "Field -> the invariant checks reading it, written out by hand; the library derives the
  same index from the bodies."
  {:take [cuts-add-up?] :cuts [cuts-add-up? only-crew?] :crew [only-crew?]})

(defn payout
  "What `cuts` come to. Both sides' `total-payout` call this one function, so the JIT
  compiles the arithmetic from one profile, and the read-method row measures the method call
  around it."
  [cuts]
  (reduce + 0 (vals cuts)))

(defprotocol Job
  (total-payout [h]    "What the cuts come to.")
  (rename       [h nm] "Retitle the job."))

;;; ------------------------------------------------------------- the library side

(rec/defproven BenchHeist [name crew take cuts]
  rec/checks
  (name [] (non-blank-string? name))
  (crew [] (crew-set? crew))
  (take [] (non-neg-int? take))
  (cuts [] (cuts-map? cuts))
  (cuts-add-up [] "cuts add up" (= take (reduce + 0 (vals cuts))))
  (only-crew [] "only crew" (every? crew (keys cuts)))

  Job
  (total-payout [h]    (payout (::cuts h)))
  (rename       [h nm] (assoc h ::name nm)))

;;; ----------------------------------------------------------- the hand-rolled side

;; The twin is the base every row is measured against: each ratio is a multiple of this code.

(defn- bad! [k] (throw (ex-info "invalid" {:k k})))

(defn m-assoc [r k v]
  (when-not ((field-preds k) v) (bad! k))
  (let [r' (assoc r k v)]
    (doseq [p (invariant-index k)] (when-not (p r') (bad! k)))
    r'))

(defrecord PlainHeist [name crew take cuts]
  Job
  (total-payout [h]    (payout (:cuts h)))
  ;; The library's `rename` runs the checks reading `::name`; `m-assoc` is that selection,
  ;; written out.
  (rename       [h nm] (m-assoc h :name nm)))

(defn m-merge [r kvs]
  (doseq [[k v] kvs] (when-not ((field-preds k) v) (bad! k)))
  (let [r' (into r kvs)]
    (doseq [p (distinct (mapcat invariant-index (keys kvs)))] (when-not (p r') (bad! nil)))
    r'))

(defn m-validate!
  "The hand-rolled `seal`: the shape checks of the keys written, then the invariant checks
  reading them."
  [r dirty]
  (doseq [k dirty] (when-not ((field-preds k) (get r k)) (bad! k)))
  (doseq [p (distinct (mapcat invariant-index dirty))] (when-not (p r) (bad! nil)))
  r)

;;; ------------------------------------------------------------------- fixtures

(def valid-cuts {:charlie 1000 :lyle 1000 :left-ear 1000})
(def base  {:name "The Italian Job" :crew #{:charlie :lyle :left-ear} :take 3000 :cuts valid-cuts})
(def qbase {::name "The Italian Job" ::crew #{:charlie :lyle :left-ear} ::take 3000 ::cuts valid-cuts})
(def r (map->PlainHeist base))
(def h (map->BenchHeist qbase))

;; Equal to what the fixtures hold but not identical to it. A write of the identical value
;; changes nothing in the library and runs no check, so the write rows use these.
(def cuts2 (into {} valid-cuts))
(def take2 (Long/valueOf 3000))

(def ^:private is15 (vec (range 15)))

(defn- m-add [r i]
  (let [who (keyword (str "m" i))]
    (-> r
        (assoc :crew (conj (:crew r) who))
        (assoc :cuts (assoc (:cuts r) who 10))
        (assoc :take (+ (:take r) 10)))))

(defn- q-add [x i]
  (let [who (keyword (str "m" i))]
    (-> x
        (assoc ::crew (conj (::crew x) who))
        (assoc ::cuts (assoc (::cuts x) who 10))
        (assoc ::take (+ (::take x) 10)))))

(defn- reads [f] (loop [i 0 acc 0] (if (< i 100) (recur (inc i) (+ acc (long (f)))) acc)))

(def ^:private untouched (rec/draft h))

(def ^:private drafts100
  "A hundred drafts of `h`, each with `::name` written. The first call checks each draft, which
  remembers the pass, so every timed call answers from that memory on both sides."
  (mapv (fn [_] (assoc (rec/draft h) ::name "n0")) (range 100)))

(def ^:private records100
  "A hundred hand-rolled records, each with `:name` written: the twin of `drafts100`."
  (mapv (fn [_] (assoc r :name "n0")) (range 100)))

;;; --------------------------------------------- a type with a check that reads a source

;; `BenchCrew` has a check that reads a source and `BenchTag` has none. The rows below write
;; only keys that no source check reads, so the library assumes that check and runs the rest on
;; the calling thread, and the source is never called; [[asked]] counts its calls.

(def asked (atom 0))

(defn on-roster
  "A source that never refuses: every crew member is on the roster. Counts its calls."
  [ks]
  (swap! asked inc)
  (into {} (map (fn [k] [k true])) ks))

(rec/defproven BenchCrew [name take crew]
  rec/checks
  (name [] (non-blank-string? name))
  (take [] (non-neg-int? take))
  (crew [] (crew-set? crew))
  (all-known [] (every? true? (vals (rec/fetch-each on-roster crew)))))

(rec/defproven BenchTag [name take]
  rec/checks
  (name [] (non-blank-string? name))
  (take [] (non-neg-int? take)))

(def ^:private small-preds {:name non-blank-string? :take non-neg-int? :crew crew-set?})

(defrecord PlainCrew [name take crew])
(defrecord PlainTag [name take])

(defn- s-merge [r kvs]
  (reduce-kv (fn [_ k v] (when-not ((small-preds k) v) (bad! k))) nil kvs)
  (into r kvs))

(defn- s-make [m]
  (reduce-kv (fn [_ k v] (when-not ((small-preds k) v) (bad! k))) nil m)
  (map->PlainTag m))

(def ^:private crew-base {:name "The Italian Job" :take 3000 :crew #{:charlie :lyle}})
(def ^:private pc (map->PlainCrew crew-base))
(def ^:private bc (map->BenchCrew {::name "The Italian Job" ::take 3000 ::crew #{:charlie :lyle}}))
(def ^:private tag-base {:name "The Italian Job" :take 3000})
(def ^:private qtag {::name "The Italian Job" ::take 3000})

;;; ------------------------------------ a wide type, a merge of the key a source check reads

;; `BenchCrewWide` has thirty int fields and `crew`, which `all-known` reads to ask [[on-roster]];
;; its twin is a plain `defrecord` of the same fields. A merge of `crew` runs that key's checks,
;; the source call among them, on both sides.

(defmacro ^:private def-crew-wide [n]
  (let [fs (map #(symbol (str "f" %)) (range n))]
    `(do (rec/defproven ~'BenchCrewWide [~@fs ~'crew]
           rec/checks
           ~@(for [f fs] `(~f [] (int? ~f)))
           (~'crew [] (crew-set? ~'crew))
           (~'all-known [] (every? true? (vals (rec/fetch-each on-roster ~'crew)))))
         (defrecord ~'PlainCrewWide [~@fs ~'crew]))))

(def-crew-wide 30)

(defn- w-merge [r kvs]
  (reduce-kv (fn [_ k v]
               (if (= k :crew)
                 (when-not (and (crew-set? v) (every? true? (vals (on-roster v)))) (bad! k))
                 (when-not (int? v) (bad! k))))
             nil kvs)
  (into r kvs))

(defn- crew-wide-entries [k]
  (assoc (into {} (for [i (range 30)] [(k (str "f" i)) (long i)])) (k "crew") #{:charlie :lyle}))

(def ^:private pcw (map->PlainCrewWide (crew-wide-entries keyword)))
(def ^:private bcw (map->BenchCrewWide (crew-wide-entries #(keyword "recognitum.bench" %))))
(def ^:private crew2 #{:charlie})

(def ^:private hundred (range 100))

(defn- crew-drafts
  "A hundred drafts of `bc`, each with `::crew` written, so each still owes its source check."
  []
  (mapv (fn [_] (assoc (rec/draft bc) ::crew crew2)) hundred))

(defn- check-all-then-seal
  "The hand-written way to seal many drafts: check them in one pass, then seal each, which runs
  nothing the pass found passing."
  [ds]
  (let [answers (rec/check-all ds rec/every)]
    (if (every? true? answers)
      (mapv rec/seal ds)
      (throw (ex-info "not every draft seals" {:answers answers})))))

;;; ------------------------------------------------------ a value doing normal map things

;; `BenchWide` has twelve fields, eleven with one check each and an optional `note` that no check
;; reads; its twin is a plain `defrecord` of the same fields. The map rows time what code that
;; only reads, compares, walks or prints a value does, the writes of `note`, which run no check,
;; and merges of `f10`, which run its one check.

(rec/defproven BenchWide [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 ^:optional note]
  rec/checks
  (f0 [] (int? f0)) (f1 [] (int? f1)) (f2 [] (int? f2)) (f3 [] (int? f3)) (f4 [] (int? f4))
  (f5 [] (int? f5)) (f6 [] (int? f6)) (f7 [] (int? f7)) (f8 [] (int? f8)) (f9 [] (int? f9))
  (f10 [] (int? f10)))

(defrecord PlainWide [f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 note])

(defn- wide-entries [k]
  (into {} (for [i (range 11)] [(k (str "f" i)) (Long/valueOf (long (+ 1000 i)))])))

(def ^:private wide-base (assoc (wide-entries keyword) :note 1))
(def ^:private wide-qbase (assoc (wide-entries #(keyword "recognitum.bench" %)) ::note 1))
(def ^:private pw (map->PlainWide wide-base))
(def ^:private pw2 (map->PlainWide wide-base))
(def ^:private bw (map->BenchWide wide-qbase))
(def ^:private bw2 (map->BenchWide wide-qbase))

(defn- keyed
  "A map of eight values of x's kind, x among them, each value to a long."
  [x note]
  (into {x 1} (for [i (range 7)] [(assoc x note (+ 5000 i)) i])))
(def ^:private pw-key (keyed pw :note))
(def ^:private bw-key (keyed bw ::note))
(def ^:private pw-set (set (keys pw-key)))
(def ^:private bw-set (set (keys bw-key)))

(defn- walk [s] (loop [s (seq s) i 0] (if s (recur (next s) (unchecked-inc i)) i)))
(defn- sum-vals [a _ v] (+ (long a) (long v)))
(defn- unprefix [m] (into {} (map (fn [[k v]] [(keyword (name k)) v])) m))
(defn- read-printed [s] (unprefix (clojure.edn/read-string {:default (fn [_ v] v)} s)))

(def map-rows
  "The map rows, each `:lib` on a `BenchWide` value against `:base` on its record twin. A row
  with `:same?` compares the two answers with it, since they differ in form."
  [{:id :get :label "get a field" :base #(get pw :f1) :lib #(get bw ::f1)}
   {:id :get-default :label "get a field, with a default" :base #(get pw :f1 :none) :lib #(get bw ::f1 :none)}
   {:id :contains :label "contains? a field" :base #(contains? pw :f1) :lib #(contains? bw ::f1)}
   {:id :count :label "count" :base #(count pw) :lib #(count bw)}
   {:id :seq :label "walk the seq" :base #(walk pw) :lib #(walk bw)}
   {:id :reduce-kv :label "reduce-kv over the values" :base #(reduce-kv sum-vals 0 pw) :lib #(reduce-kv sum-vals 0 bw)}
   {:id :keys :label "walk the keys" :base #(walk (keys pw)) :lib #(walk (keys bw))}
   {:id :vals :label "sum the vals" :base #(reduce + 0 (vals pw)) :lib #(reduce + 0 (vals bw))}
   {:id :into-map :label "into {}" :base #(into {} pw) :lib #(into {} bw)}
   {:id :select-keys :label "select-keys of two fields" :base #(select-keys pw [:f1 :f2]) :lib #(select-keys bw [::f1 ::f2])}
   {:id :equal :label "= of two equal values" :base #(= pw pw2) :lib #(= bw bw2)}
   {:id :hash :label "hash" :base #(hash pw) :lib #(hash bw)
    :same? (fn [_ mine] (= mine (hash (into {} bw))))}
   {:id :map-key :label "look up a value as a map key" :base #(get pw-key pw2) :lib #(get bw-key bw2)}
   {:id :set :label "contains? of a set of values" :base #(contains? pw-set pw2) :lib #(contains? bw-set bw2)}
   {:id :assoc-unchecked :label "assoc a field no check reads" :base #(assoc pw :note 7) :lib #(assoc bw ::note 7)}
   {:id :update-unchecked :label "update a field no check reads" :base #(update pw :note inc) :lib #(update bw ::note inc)}
   {:id :dissoc-unchecked :label "dissoc a field no check reads" :base #(dissoc pw :note) :lib #(dissoc bw ::note)}
   {:id :merge-unchecked :label "merge a field no check reads" :base #(merge pw {:note 7}) :lib #(merge bw {::note 7})}
   {:id :merge-checked :label "merge a field one check reads" :base #(merge pw {:f10 7}) :lib #(merge bw {::f10 7})}
   {:id :merge-two :label "merge two fields, one check reads one" :base #(merge pw {:note 7 :f10 8})
    :lib #(merge bw {::note 7 ::f10 8})}
   {:id :into-one :label "into a field no check reads" :base #(into pw {:note 7}) :lib #(into bw {::note 7})}
   {:id :conj-one :label "conj a field no check reads" :base #(conj pw [:note 7]) :lib #(conj bw [::note 7])}
   {:id :pr-str :label "pr-str" :base #(pr-str pw) :lib #(pr-str bw)
    :same? (fn [theirs mine] (= (read-printed theirs) (read-printed mine)))}])

;;; ----------------------------------------------------------------------- rows

(def rows
  "Each row times `:lib` against `:base`, the hand-rolled twin doing the same work. `:scale`
  divides the call counts for the slow rows."
  [{:id :read :label "read a field (x100)" :against :twin
    :base #(reads (fn [] (:take r))) :lib #(reads (fn [] (::take h)))}
   {:id :write-name :label "write :name, no invariant" :against :twin
    :base #(m-assoc r :name "x") :lib #(assoc h ::name "x")}
   {:id :write-cuts :label "write :cuts, two invariants" :against :twin
    :base #(m-assoc r :cuts cuts2) :lib #(assoc h ::cuts cuts2)}
   {:id :write-identical :label "write :cuts, the identical value" :against :twin
    :base #(m-assoc r :cuts valid-cuts) :lib #(assoc h ::cuts valid-cuts)}
   {:id :merge :label "merge two fields" :against :twin
    :base #(m-merge r {:take take2 :cuts cuts2}) :lib #(merge h {::take take2 ::cuts cuts2})}
   {:id :construct :label "construct (draft, into, seal)" :against :twin
    :base #(m-validate! (map->PlainHeist base) [:name :crew :take :cuts])
    :lib #(rec/seal (into (rec/draft BenchHeist) qbase))}
   {:id :construct-map :label "construct (map->BenchHeist)" :against :twin
    :base #(m-validate! (map->PlainHeist base) [:name :crew :take :cuts])
    :lib #(map->BenchHeist qbase)}
   {:id :read-method :label "read method on a sealed value" :against :twin
    :base #(total-payout r) :lib #(total-payout h)}
   {:id :write-method :label "write method on a sealed value" :against :twin
    :base #(rename r "x") :lib #(rename h "x")}
   {:id :rename-1 :label "one rename in a draft" :against :twin
    :base #(m-validate! (assoc r :name "n0") [:name])
    :lib #(rec/seal (assoc (rec/draft h) ::name "n0"))}
   {:id :rename-15 :label "15 renames in a draft" :against :twin :scale 4
    :base #(m-validate! (reduce (fn [x i] (assoc x :name (str "n" i))) r is15) [:name])
    :lib #(rec/seal (reduce (fn [x i] (assoc x ::name (str "n" i))) (rec/draft h) is15))}
   {:id :add-1 :label "one add-member (3 writes) in a draft" :against :twin
    :base #(m-validate! (m-add r 0) [:crew :cuts :take])
    :lib #(rec/seal (q-add (rec/draft h) 0))}
   {:id :add-15 :label "15 add-members in a draft" :against :twin :scale 4
    :base #(m-validate! (reduce m-add r is15) [:crew :cuts :take])
    :lib #(rec/seal (reduce q-add (rec/draft h) is15))}
   {:id :seal-pending :label "seal, one pending check" :against :twin
    :base #(m-validate! (assoc r :name "n0") [:name])
    :lib #(rec/seal (assoc (rec/draft h) ::name "n0"))}
   {:id :seal-untouched :label "seal an untouched draft" :against :twin
    :base #(m-validate! r []) :lib #(rec/seal untouched)}
   {:id :check-all :label "check-all over 100 drafts" :against :twin :scale 50
    :base #(mapv (fn [x] (m-validate! x [:name]) true) records100) :lib #(rec/check-all drafts100 ::name)}
   {:id :seal-all :label "seal-all of 100 drafts with a source check" :against :check-all-then-seal :scale 50
    :base #(check-all-then-seal (crew-drafts)) :lib #(rec/seal-all (crew-drafts))}
   {:id :seal-all-alone :label "seal-all of 100 drafts against a seal of each" :against :seal-each :scale 50
    :base #(mapv rec/seal (crew-drafts)) :lib #(rec/seal-all (crew-drafts))}
   {:id :merge-sourced :label "merge two fields, a source check assumed" :against :twin
    :base #(s-merge pc {:name "x" :take take2}) :lib #(merge bc {::name "x" ::take take2})}
   {:id :construct-small :label "construct a two-field type (map->)" :against :twin
    :base #(s-make tag-base) :lib #(map->BenchTag qtag)}
   {:id :merge-sourced-wide :label "merge a key a source check reads, 30+1 fields" :against :twin
    :base #(w-merge pcw {:crew crew2}) :lib #(merge bcw {::crew crew2})}])

(def row (into {} (map (juxt :id identity)) (concat rows map-rows)))

;;; ---------------------------------------------------------------- the measurement

(defn- ns-per
  "Nanoseconds per call of `f` over `iters` calls. The last result is kept and inspected, so
  the JIT cannot drop the call as dead code."
  [iters f]
  (let [sink (volatile! nil)
        t0   (System/nanoTime)]
    (dotimes [_ iters] (vreset! sink (f)))
    (let [elapsed (- (System/nanoTime) t0)]
      (when (nil? @sink) (throw (ex-info "the shape being measured produced nothing" {})))
      (/ (double elapsed) iters))))

(defn ratio
  "`[multiple base-ns lib-ns]` for the row `{:keys [base lib scale]}`: what `lib` costs as a
  multiple of what `base` costs.

  Untimed rounds first, for a quarter of a second at least, so the JIT has compiled both
  sides before either is timed: a count of rounds is not enough, since the compiler works in
  the background. Then interleaved, and the best
  of seven trials on each side: whatever the machine did during a trial it did to both, and
  the minimum is the trial least of it landed on."
  [{:keys [base lib scale] :or {scale 1}}]
  (let [warm (max 1 (quot 2000 scale))
        n    (max 1 (quot 5000 scale))
        until (+ (System/nanoTime) 250000000)]
    (loop [i 0]
      (ns-per warm base) (ns-per warm lib)
      (when (or (< i 10) (< (System/nanoTime) until)) (recur (inc i))))
    (let [[b l] (reduce (fn [[b l] _] [(min b (ns-per n base)) (min l (ns-per n lib))])
                        [Double/MAX_VALUE Double/MAX_VALUE]
                        (range 7))]
      [(/ l b) b l])))

(defn run
  "Prints every row: base ns, library ns, and the multiple."
  []
  (println (format "%-50s %10s %10s %8s" "" "base" "library" "ratio"))
  (doseq [{:keys [label] :as rw} (concat rows map-rows)]
    (let [[x b l] (ratio rw)]
      (println (format "%-50s %10.1f %10.1f %7.2fx" label b l x)))))
