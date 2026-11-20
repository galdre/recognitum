(ns recognitum.docs-test
  "The examples of the documents under `docs/` give the results they show. Every block fenced
  as `clojure` runs: the blocks of one file in order, in the namespace that the file's first
  block declares with an `ns` form. A comment `;; => x` after a form, on its line or the next,
  is the form's value. A comment `;; SomeException: message` is the class and the message of
  what the forms before it throw. Either continues on the comment lines after it that begin
  with `;;` and two spaces. Messages are compared with every run of whitespace as one space.
  A file fences what is not code to run, such as a message or a command, as `text`. A fence
  may be indented, as inside a list item. The test fails for a fence line that belongs to no
  block, and for a comment in a `clojure` block that shows a result or a throw in another
  spelling, since nothing would compare it."
  (:require
   [clojure.java.io :as io]
   [clojure.string :as str]
   [clojure.test :refer [deftest is testing]])
  (:import
   [java.io File]))

(defn- documents
  "The paths of the Markdown files under `root`, sorted."
  [root]
  (sort (for [^File f (file-seq (io/file root))
              :when (and (.isFile f) (str/ends-with? (.getName f) ".md"))]
          (str f))))

(defn- fences
  "The fenced blocks of `text` as [language code] pairs, in order. The code of an indented
  block is given without the indentation of its fence."
  [text]
  (mapv (fn [[_ indent language code]]
          [language (str/join "\n" (map #(cond-> % (str/starts-with? % indent) (subs (count indent)))
                                        (str/split-lines code)))])
        (re-seq #"(?ms)^([ \t]*)```(\S*)[ \t]*\n(.*?)\n[ \t]*```[ \t]*$" text)))

(defn- fence-lines
  "How many lines of `text` open or close a fence."
  [text]
  (count (filter #(str/starts-with? (str/triml %) "```") (str/split-lines text))))

(defn- unread-expectations
  "The lines of `code` that show a result or a throw in a spelling that [[steps]] does not
  read: an arrow that is not `;; =>`, or a comment that names an exception class and is not
  `;; SomeException: message`."
  [code]
  (filter #(or (and (re-find #";+\s*=>" %) (not (str/includes? % ";; =>")))
               (and (re-find #"^\s*;+\s*(?:[A-Z]\w*)?(?:Exception|Error)\w*\b" %)
                    (not (re-find #"^;; (?:[A-Z][A-Za-z]*)?(?:ExceptionInfo|Exception|Error): " %))))
          (str/split-lines code)))

(def ^:private throw-line #"^;; ((?:[A-Z][A-Za-z]*)?(?:ExceptionInfo|Exception|Error)): (.*)$")

(defn- continued
  "[text more]: `text` continued by the comment lines at the head of `lines`, and the rest."
  [text lines]
  (let [[cont more] (split-with #(str/starts-with? % ";;  ") lines)]
    [(str/join "\n" (cons text (map #(subs % 2) cont))) more]))

(defn- steps
  "The block as [code expectation] pairs: the code before each expectation, and the
  expectation as [:value text], [:throws class-name message] or nil."
  [code]
  (loop [[line & more :as lines] (str/split-lines code), pending [], out []]
    (cond
      (empty? lines)
      (cond-> out (some (complement str/blank?) pending) (conj [(str/join "\n" pending) nil]))

      (str/includes? line ";; =>")
      (let [[c v] (str/split line #";; =>" 2)
            [value more] (continued v more)]
        (recur more [] (conj out [(str/join "\n" (conj pending c)) [:value value]])))

      (re-find throw-line line)
      (let [[_ class-name message] (re-find throw-line line)
            [message more] (continued message more)]
        (recur more [] (conj out [(str/join "\n" pending) [:throws class-name message]])))

      :else (recur more (conj pending line) out))))

(defn- one-space [s] (str/trim (str/replace s #"\s+" " ")))

(defn- thrown
  "[class-name message] of what running `code` throws: of the first throwable in the chain of
  causes whose class has the simple name `class-name`, else of the outermost. `[:returned]`
  where `code` returns."
  [code class-name]
  (try (load-string code) [:returned]
       (catch Throwable e
         (let [chain (take-while some? (iterate ex-cause e))
               ^Throwable t (or (first (filter #(= class-name (.getSimpleName (class %))) chain)) e)]
           [(.getSimpleName (class t)) (one-space (str (ex-message t)))]))))

(defn- declared-ns
  "The name of the namespace that `code` declares in its first form, or nil."
  [code]
  (let [form (try (read-string code) (catch Exception _ nil))]
    (when (and (seq? form) (= 'ns (first form))) (second form))))

(defn- run-document!
  "Runs every `clojure` block of the document at `path`, each step against its expectation."
  [path]
  (let [text (slurp path)
        blocks (fences text)
        code (mapv second (filter #(= "clojure" (first %)) blocks))
        ns-name (some-> (first code) declared-ns)]
    (testing path
      (is (every? #{"clojure" "text"} (map first blocks))
          "every block is fenced as clojure, which runs, or as text")
      (is (= (* 2 (count blocks)) (fence-lines text))
          "every fence line opens or closes a block that the test reads")
      (is (empty? (mapcat unread-expectations code))
          "every result is written as ;; => x, and every throw as ;; SomeException: message")
      (when (seq code)
        (is (some? ns-name) "the first clojure block opens with an ns form")
        (is (nil? (some-> ns-name find-ns)) "no loaded namespace has the document's name")
        (when (and ns-name (nil? (find-ns ns-name)))
          (try
            (doseq [block code, [step [kind a b]] (steps block)]
              ;; The first step makes the namespace; each later step runs in it.
              (binding [*ns* (or (find-ns ns-name) *ns*)]
                (case kind
                  ;; The value is read after the step ran, in the namespace the step may have made.
                  :value (let [actual (load-string step)
                               expected (binding [*ns* (or (find-ns ns-name) *ns*)] (read-string a))]
                           (is (= expected actual) step))
                  :throws (is (= [a (one-space b)] (thrown step a)) step)
                  nil (load-string step))))
            (finally (remove-ns ns-name))))))))

(deftest the-documents-give-the-results-they-show
  (let [paths (documents "docs")]
    (is (seq paths))
    (run! run-document! paths)))
