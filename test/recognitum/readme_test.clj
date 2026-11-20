(ns recognitum.readme-test
  "The README's examples give the results they show. Its blocks are written and run as the
  blocks of a document under `docs/` are: `recognitum.docs-test` states the rules."
  (:require
   [clojure.string :as str]
   [clojure.test :refer [deftest is]]
   [recognitum.docs-test]))

(deftest the-readme-gives-the-results-it-shows
  (is (str/includes? (slurp "README.md") "\n```clojure\n") "the README has a block that runs")
  (#'recognitum.docs-test/run-document! "README.md"))
