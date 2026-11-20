#!/usr/bin/env bb
;; Runs clj-kondo over the shared corpus and compares each file's findings with
;; the `;; expect {...}` map in its header.
;;
;; Header keys:
;;   :report  [{:at [line col] :level :error|:warning :names "token" :kondo "message"} ...]
;;            the tool-neutral expectation; :kondo is clj-kondo's exact message.
;;            An entry with :tool :compiler is not expected from clj-kondo.
;;   :kondo   optional: overrides what clj-kondo is expected to report (as :report entries).
;;   :docs    optional: {var docstring ...}, each var's docstring, under clj-kondo's analysis
;;            (with the warm cache) and at run time.
;;   :kondo-docs optional: overrides :docs for clj-kondo's analysis; nil for no docstring.
;;   :cache-from optional: [file ...]: the file is also linted alone, in a run of its own, with a
;;            fresh cache that holds the library and these files; it then reports what :report
;;            (or :kondo) says, and its vars have the docstrings :docs gives. So what the hook
;;            learns of another namespace through the cache alone is tested.
;;   :outline optional: [var ...], every var the file defines under clj-kondo's analysis (with
;;            the warm cache), which an editor lists in the file's outline.
;;   :cold    :same, or entries: what clj-kondo reports when the file is linted
;;            alone with a fresh cache that holds only recognitum.core.
;;
;; Warm: the whole corpus, linted twice with one cache, with the library's sources. Cold: each
;; file alone, with a fresh cache that holds only the library. The hook and its config are the
;; ones the library exports.
;; Usage: bb test/corpus/corpus_check.bb
(require '[babashka.process :refer [shell]]
         '[babashka.fs :as fs]
         '[clojure.edn :as edn]
         '[clojure.string :as str])

(def root (str (fs/parent (fs/absolutize *file*))))
(def project (str (fs/parent (fs/parent root))))
(def library [(str project "/src")])
(def config-dir
  (let [d (fs/create-temp-dir)]
    (spit (str d "/config.edn")
          (pr-str {:config-paths [(str project "/resources/clj-kondo.exports/recognitum/recognitum")]
                   :output {:exclude-files ["/src/"]}}))
    (str d)))

(defn header [f]
  (let [lines (take-while #(str/starts-with? % ";;") (str/split-lines (slurp (str root "/" f))))
        text (str/join "\n" (map #(subs % 2) lines))
        i (str/index-of text "expect")]
    (edn/read-string (subs text (+ i (count "expect"))))))

(defn lint
  "clj-kondo's output for paths, linted with cache, with its analysis when analysis? is true."
  ([cache paths] (lint cache paths false))
  ([cache paths analysis?]
   (let [{:keys [out]} (apply shell {:dir root :out :string :continue true}
                              "clj-kondo" "--cache-dir" (str cache) "--config-dir" config-dir
                              "--config" (pr-str {:analysis analysis? :output {:format :edn}})
                              "--lint" paths)]
     (edn/read-string out))))

(defn findings [cache paths]
  (group-by :filename (:findings (lint cache paths))))

(defn docs-of
  "[var docstring] for each var of file f named in names, under the analysis in output."
  [output f names]
  (set (for [{:keys [name doc filename]} (:var-definitions (:analysis output))
             :when (and (= f filename) (contains? names name))]
         [name doc])))

(defn as-set [fs]
  (set (for [{:keys [row col level message]} fs] [row col level message])))

(defn expected [entries]
  (set (for [{[row col] :at :keys [level kondo tool]} entries
             :when (not= tool :compiler)]
         [row col level kondo])))

(def files (sort (map #(str (fs/relativize root %)) (fs/glob root "**.{clj,cljc}"))))

(def warm-cache (fs/create-temp-dir))

(def warm
  (do (findings warm-cache (into library ["usage" "mistakes" "extra"]))
      (findings warm-cache (into library ["usage" "mistakes" "extra"]))))

(defn cold [f]
  (let [cache (fs/create-temp-dir)]
    (findings cache library)
    (get (findings cache (conj library f)) f)))

(defn cached
  "clj-kondo's output, with its analysis, for f linted alone with a fresh cache that holds the
  library and sources."
  [f sources]
  (let [cache (fs/create-temp-dir)]
    (findings cache (into library sources))
    (lint cache (conj library f) true)))

(def failures (atom 0))

(defn compare! [label f want got]
  (if (= want got)
    (println "ok  " label f)
    (do (swap! failures inc)
        (println "FAIL" label f)
        (doseq [x (sort (remove got want))] (println "     missing   " x))
        (doseq [x (sort (remove want got))] (println "     unexpected" x)))))

(doseq [f files]
  (let [h (header f)
        want (expected (or (:kondo h) (:report h)))
        got-warm (as-set (get warm f))]
    (compare! "warm" f want got-warm)
    (compare! "cold" f (if (= :same (:cold h)) want (expected (:cold h))) (as-set (cold f)))
    (when-let [sources (:cache-from h)]
      (let [out (cached f sources)]
        (compare! "cached" f want (as-set (filter #(= f (:filename %)) (:findings out))))
        (when-let [docs (or (:kondo-docs h) (:docs h))]
          (compare! "cached docs" f (set docs) (docs-of out f docs)))))))

(def analysed
  "clj-kondo's output, with its analysis, for the corpus linted with the warm cache."
  (lint warm-cache ["usage" "mistakes" "extra"] true))

(def var-definitions
  "clj-kondo's analysis of the vars the corpus defines, the hook's own included."
  (:var-definitions (:analysis analysed)))

(doseq [f files
        :let [h (header f) want (or (:kondo-docs h) (:docs h))]
        :when want]
  (compare! "docs" f (set want) (docs-of analysed f want)))

(doseq [f files
        :let [want (:outline (header f))]
        :when want]
  (compare! "outline" f (set want)
            (set (for [{:keys [name filename]} var-definitions :when (= f filename)] name))))

(def snake-vars
  "The vars whose names hold an underscore: a kebab-case rule of a user's linter reports each."
  (sort (set (for [{:keys [name]} var-definitions
                   :when (str/includes? (str name) "_")]
               name))))

(if (empty? snake-vars)
  (println "ok   kebab-case var names")
  (do (swap! failures inc)
      (println "FAIL kebab-case var names:" (str/join " " snake-vars))))

(println (if (zero? @failures) "all files as expected" (str @failures " mismatches")))
(System/exit (if (zero? @failures) 0 1))
