(ns recognitum.readme-test
  "The README's examples give the results they show. A block that shows results runs line by
  line: a comment `;; => x` after a form, on its line or the next, is the form's value, and
  `;; ExceptionInfo: message` is the message it throws, continued on the comment lines after
  it. The Heist's blocks are written in `crew.heist` and run in `demo.heist`."
  (:require
   [clojure.edn :as edn]
   [clojure.string :as str]
   [clojure.test :refer [deftest is testing]]
   [demo.authz]
   [demo.guild :as guild]
   [demo.heist]
   [demo.orders]
   [demo.permissions :as perms]
   [demo.potion]
   [recognitum.core :as rec]))

(def ^:private readme (slurp "README.md"))

(def ^:private blocks
  (mapv second (re-seq #"(?s)```clojure\n(.*?)\n```" readme)))

(defn- block
  "The one block of the README that holds `text`."
  [text]
  (let [found (filterv #(str/includes? % text) blocks)]
    (is (= 1 (count found)) (str "one README block holds " (pr-str text)))
    (first found)))

(defn- as-heist [s] (str/replace s "crew.heist" "demo.heist"))

(defn- steps
  "The block as [code expectation] pairs: the code before each expectation, and the
  expectation as [:value text] or [:throws message]."
  [text]
  (loop [[line & more :as lines] (str/split-lines text), code [], out []]
    (cond
      (empty? lines)
      (cond-> out (seq code) (conj [(str/join "\n" code) nil]))

      (str/includes? line ";; =>")
      (let [[c v] (str/split line #";; =>" 2)
            [cont rest] (split-with #(str/starts-with? % ";;  ") more)]
        (recur rest [] (conj out [(str/join "\n" (conj code c))
                                  [:value (str/join "\n" (cons v (map #(subs % 2) cont)))]])))

      (str/starts-with? line ";; ExceptionInfo: ")
      (let [[cont rest] (split-with #(str/starts-with? % ";;  ") more)]
        (recur rest [] (conj out [(str/join "\n" code)
                                  [:throws (str/join "\n" (cons (subs line (count ";; ExceptionInfo: "))
                                                                (map #(subs % 3) cont)))]])))

      :else (recur more (conj code line) out))))

(defn- thrown-message
  "The message of the ex-info that running `code` threw, unwrapped from the compiler's
  exception, or `:returned`."
  [code]
  (try (load-string code) :returned
       (catch Throwable e
         (ex-message (first (filter #(instance? clojure.lang.ExceptionInfo %)
                                    (take-while some? (iterate ex-cause e))))))))

(defn- run-block!
  "Runs the steps of `text` in the namespace `ns`, each against its expectation, with `subst`
  applied to the README's text of each expectation."
  [ns text subst]
  (binding [*ns* (the-ns ns)]
    (doseq [[code [kind expected]] (steps text)]
      (case kind
        :value (is (= (read-string (subst expected)) (load-string code)) code)
        :throws (is (= (subst expected) (thrown-message code)) code)
        nil (load-string code)))))

(defn- with-scratch-vars
  "Calls `f`, then unmaps the vars it defined in `ns`."
  [ns f]
  (let [before (set (keys (ns-interns ns)))]
    (try (f)
         (finally (doseq [v (keys (ns-interns ns)) :when (not (before v))] (ns-unmap ns v))))))

(defn- source-holds? [file form-text] (str/includes? (slurp file) form-text))

;;; ------------------------------------------------------------------ the Heist

(deftest the-heist-is-the-demo-heist
  (let [form (block "(name    [] \"the job has a name\"")]
    (is (source-holds? "dev/demo/heist.clj" (subs form (str/index-of form "(rec/defproven"))))))

(deftest the-heist-blocks-give-their-results
  (with-scratch-vars 'demo.heist
    (fn []
      (run-block! 'demo.heist (block "(map->Heist {::name \"Job\"") as-heist)
      (binding [*ns* (the-ns 'demo.heist)]
        (load-string "(def job (map->Heist {::name \"Job\" ::crew #{\"Charlie\" \"Stella\"} ::take 2000
                                             ::cuts {\"Charlie\" 1000 \"Stella\" 1000}}))"))
      (run-block! 'demo.heist (block "(merge job {::take 3000") as-heist))))

(deftest the-probe-and-the-absent-field-blocks-give-their-results
  (run-block! 'demo.heist (block "(rec/probe Heist {::name \"Job\" ::crew #{\"Charlie\"} ::take 10") as-heist)
  (run-block! 'demo.heist (block "(map->Heist {::name \"Bank job\"") as-heist))

(deftest the-failure-report-is-the-report-of-a-negative-take
  (let [shown (edn/read-string (as-heist (block "{:failed  {:crew.heist/take")))
        d (into (rec/draft demo.heist.Heist)
                {:demo.heist/name "Job" :demo.heist/crew #{"Charlie"} :demo.heist/take -1
                 :demo.heist/cuts {}})]
    (is (= shown (rec/check d rec/every)))))

(deftest seal-all-and-drafting-return-sealed-values
  (block "(rec/seal-all {:jobs [draft-1 draft-2] :backup draft-3})")
  (let [d #(into (rec/draft demo.heist.Heist) demo.heist/italian-job)
        {:keys [jobs backup] :as sealed} (rec/seal-all {:jobs [(d) (d)] :backup (d)})]
    (is (= #{:jobs :backup} (set (keys sealed))))
    (is (vector? jobs))
    (is (every? rec/sealed? (conj jobs backup))))
  (block "(rec/drafting-all [job-1 job-2]")
  (let [rename (fn [heist n] (rec/drafting heist #(assoc % :demo.heist/name n)))]
    (is (rec/sealed? (rename demo.heist/italian-job "The Bank Job")))
    (is (every? rec/sealed? (rec/drafting-all [demo.heist/italian-job demo.heist/italian-job]
                                              #(mapv (fn [j] (rename j "Again")) %))))))

(def ^:private scratch 'recognitum.readme-test.crew)

(deftest a-redefinition-refuses-old-values-and-old-constructors
  (let [ns (create-ns scratch)
        define "(rec/defproven Heist [name take] rec/checks (name [] (string? name)) (take [] (int? take)))"
        as-scratch #(str/replace % "crew.heist" (str scratch))]
    (binding [*ns* ns]
      (refer-clojure)
      (alias 'rec 'recognitum.core)
      (load-string define)
      (load-string "(def old-heist (map->Heist {::name \"Job\" ::take 1}))")
      (load-string "(def make map->Heist)")
      (load-string define)
      (doseq [[form shown] [["(assoc old-heist ::take 12)" "(assoc old-heist ::take 12)\n"]
                            ["(make {::name \"Ocean\" ::take 1})" "(make {::name \"Ocean\" ...})\n"]]]
        (let [text (block shown)
              lines (map #(subs % 3) (filter #(str/starts-with? % ";; ") (str/split-lines text)))
              expected (as-scratch (str/join " " (cons (subs (first lines) (count "ExceptionInfo: "))
                                                       (rest lines))))]
          (is (= expected (thrown-message form))))))
    (remove-ns scratch)))

;;; ------------------------------------------------------------------ the uses of a probe

(deftest the-uses-of-a-probe-are-the-demos-and-give-their-results
  (is (source-holds? "dev/demo/heist.clj" (block "(defn form-errors")))
  (run-block! 'demo.heist (block "(form-errors {::name") identity)
  (doseq [text ["(defn under-limit" "(defn valid-on-the-day"]]
    (is (source-holds? "dev/demo/authz.clj" (block text))))
  (doseq [form (conj (str/split (block "(defn import-problems") #"\n\n") (block "(defn upload-problems"))]
    (is (source-holds? "dev/demo/orders.clj" form)))
  (perms/restore!)
  (with-scratch-vars 'demo.authz
    (fn []
      (run-block! 'demo.authz (block "(def waiting") identity)
      (perms/revoke! "dana" :refund 42)
      (try (run-block! 'demo.authz (block "(def issued") identity)
           (finally (perms/restore!)))))
  (run-block! 'demo.orders (block "(import-problems\n") identity)
  (run-block! 'demo.orders (block "(upload-problems #{") identity))

;;; ------------------------------------------------------------------ the Potion

(deftest the-potion-is-the-demo-potion
  (doseq [text ["(rec/defconcern shop" "(rec/defproven-in Potion" "(rec/defcontext on-the-shelf"]]
    (is (source-holds? "dev/demo/potion.clj" (block text))))
  (doseq [form (str/split (block "(defn- gate") #"\n\n")]
    (is (source-holds? "dev/demo/potion.clj" form))))

(deftest the-potion-blocks-give-their-results
  (with-scratch-vars 'demo.potion
    (fn []
      (reset! guild/calls [])
      (run-block! 'demo.potion (block "(def brewed") identity)
      (run-block! 'demo.potion (block "(def mended") identity)
      (testing "the blocks of the section on contexts"
        (let [text (block "(rec/seal bottled at-court)")
              before (subs text 0 (str/index-of text "(identical? relabelled"))
              after (subs text (str/index-of text "(identical? relabelled"))]
          (run-block! 'demo.potion before identity)
          (testing "the label's write forgot only the checks that read the label"
            (is (= #{:demo.potion/label :demo.potion/labelled}
                   (apply disj (rec/checks-of rec/every demo.potion.Potion)
                          (rec/proven-checks @(ns-resolve 'demo.potion 'relabelled))))))
          (run-block! 'demo.potion after identity)))
      (testing "the sinks refuse what their context does not prove"
        (run-block! 'demo.potion (block "(sell! (into {} relabelled))") identity))
      (is (seq @guild/calls) "the shop's checks read the guild"))))
