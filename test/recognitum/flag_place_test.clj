(ns recognitum.flag-place-test
  "A clause's concerns and `:override` follow its waits. Metadata on a clause, its name, its
  waits or the head of a section is refused, since the macros read none there: dropped, a
  concern would leave its check out of every selection by it, which would pass without running
  it."
  (:require
   [clojure.test :refer [deftest is testing]]
   [recognitum.core :as rec]))

(rec/defconcern permission "Checks on the acting user's rights.")

(rec/defchecks positives [x]
  rec/checks
  (x-positive [] (pos? x)))

(defprotocol Labelled (label [x]))

(defn- refusal [form]
  (try (binding [*ns* (the-ns 'recognitum.flag-place-test)] (eval form)) nil
       (catch clojure.lang.Compiler$CompilerException e (:message (ex-data (ex-cause e))))))

(defn- remedy
  "The remedy a refusal of metadata names, for clause `nm` and flag `k`."
  [nm k]
  (str ": a clause takes no metadata; its concerns and :override go after its waits, as in ("
       nm " [waits] " k " body)"))

(deftest metadata-on-a-clause-is-refused
  (doseq [head '[rec/defproven rec/defproven-in]]
    (testing head
      (is (= (str "^::permission on the clause never" (remedy 'never "::permission"))
             (refusal (list head 'T '[a] 'rec/checks '^::permission (never [] (= a :never))))))
      (is (= (str "^:override on the clause recognitum.flag-place-test/x-positive"
                  (remedy 'recognitum.flag-place-test/x-positive ":override"))
             (refusal (list head 'T '[a] 'positives '(x [] a)
                            'rec/checks '^:override (recognitum.flag-place-test/x-positive [] true)))))))
  (testing "defchecks"
    (is (= (str "^::permission on the clause never" (remedy 'never "::permission"))
           (refusal '(rec/defchecks b [a] rec/checks ^::permission (never [] (= a :never)))))))
  (testing "metadata that names nothing the macros know"
    (is (= (str "^{:doc \"x\"} on the clause never" (remedy 'never "::concern"))
           (refusal '(rec/defchecks b [a] rec/checks ^{:doc "x"} (never [] (= a :never))))))))

(deftest metadata-on-a-clause-name-is-refused
  (doseq [head '[rec/defproven rec/defproven-in]]
    (testing head
      (is (= (str "^::permission on the name of never" (remedy 'never "::permission"))
             (refusal (list head 'T '[a] 'rec/checks '(^::permission never [] (= a :never))))))
      (is (= (str "^:override on the name of recognitum.flag-place-test/x-positive"
                  (remedy 'recognitum.flag-place-test/x-positive ":override"))
             (refusal (list head 'T '[a] 'positives '(x [] a)
                            'rec/checks '(^:override recognitum.flag-place-test/x-positive [] true)))))))
  (testing "defchecks"
    (is (= (str "^::permission on the name of never" (remedy 'never "::permission"))
           (refusal '(rec/defchecks b [a] rec/checks (^::permission never [] (= a :never)))))))
  (testing "a type hint, too"
    (is (= (str "^{:tag String} on the name of never" (remedy 'never "::concern"))
           (refusal '(rec/defchecks b [a] rec/checks (^String never [] (str a))))))))

(deftest metadata-on-a-clause-waits-is-refused
  (doseq [head '[rec/defproven rec/defproven-in]]
    (testing head
      (is (= (str "^::permission on the waits of never" (remedy 'never "::permission"))
             (refusal (list head 'T '[a] 'rec/checks '(never ^::permission [] (= a :never))))))))
  (testing "defchecks"
    (is (= (str "^:override on the waits of never" (remedy 'never ":override"))
           (refusal '(rec/defchecks b [a] rec/checks (never ^:override [] (= a :never))))))))

(deftest metadata-on-a-section-head-is-refused
  (doseq [head '[rec/defproven rec/defproven-in]]
    (testing head
      (is (= (str "^::permission on rec/checks" (remedy 'name "::permission"))
             (refusal (list head 'T '[a] '^::permission rec/checks '(never [] (= a :never))))))
      (is (= (str "^::permission on Labelled" (remedy 'name "::permission"))
             (refusal (list head 'T '[a] 'rec/checks '(ok [] true)
                            '^::permission Labelled '(label [this] "t")))))
      (is (= (str "^::permission on Comparable" (remedy 'name "::permission"))
             (refusal (list head 'T '[a] 'rec/checks '(ok [] true)
                            '^::permission Comparable '(compareTo [this o] 0)))))))
  (testing "defchecks"
    (is (= (str "^:override on rec/checks" (remedy 'name ":override"))
           (refusal '(rec/defchecks b [a] ^:override rec/checks (never [] (= a :never))))))))

(def ^:private input-remedy
  ": an input clause takes no concern or :override; they go after a check's waits")

(deftest a-flag-on-an-input-clause-is-refused
  (is (= (str "^::permission on input clause x of positives" input-remedy)
         (refusal '(rec/defproven T [a] positives ^::permission (x [] a) rec/checks (ok [] true)))))
  (is (= (str "^:override on input clause x of positives" input-remedy)
         (refusal '(rec/defproven T [a] positives ^:override (x [] a) rec/checks (ok [] true)))))
  (is (= (str "^::permission on the name of input clause x of positives" input-remedy)
         (refusal '(rec/defproven T [a] positives (^::permission x [] a) rec/checks (ok [] true)))))
  (is (= (str "::permission on input clause x of positives" input-remedy)
         (refusal '(rec/defproven T [a] positives (x [] ::permission a) rec/checks (ok [] true)))))
  (is (= (str "#{:override} on input clause x of positives" input-remedy)
         (refusal '(rec/defproven T [a] positives (x [] #{:override} a) rec/checks (ok [] true))))))

(defn- make [form tname]
  (binding [*ns* (the-ns 'recognitum.flag-place-test)]
    (eval form)
    (eval (list 'fn '[m] (list (symbol (str "map->" tname)) 'm)))))

(rec/defconcern audit "Checks an auditor reads.")

(deftest flags-after-the-waits-carry-concerns-and-override
  (testing "a keyword"
    (let [v ((make '(rec/defproven-in K [a] rec/checks (never [] ::permission (= a :never))) 'K) {::a 1})]
      (is (false? (rec/proves? v ::permission)))
      (is (= #{::never} (rec/checks-of ::permission (class v))))))
  (testing "a set, and a docstring after it"
    (let [v ((make '(rec/defproven-in S [a] rec/checks
                                      (never [] #{::permission ::audit} "never passes" (= a :never)))
                   'S)
             {::a 1})]
      (is (= #{::never} (rec/checks-of ::audit (class v)) (rec/checks-of ::permission (class v))))
      (is (nil? (refusal '(rec/defchecks documented [a] rec/checks
                            (dnever [] #{::permission ::audit} "never passes" (= a :never))))))
      (is (= "never passes" (:doc (meta (resolve 'recognitum.flag-place-test/dnever)))))
      (is (= #{::permission ::audit} (:concerns @(resolve 'recognitum.flag-place-test/dnever))))))
  (testing ":override, alone or with a concern"
    (is (nil? (refusal '(rec/defproven O [a] positives (x [] a)
                                       rec/checks (recognitum.flag-place-test/x-positive [] :override true)))))
    (let [v ((make '(rec/defproven-in O2 [a] positives (x [] a)
                                      rec/checks (recognitum.flag-place-test/x-positive [] #{:override ::audit} (pos? a)))
                   'O2)
             {::a -1})]
      (is (false? (rec/proves? v ::audit)))))
  (testing "a keyword or set alone after the waits is the body"
    (let [v ((make '(rec/defproven-in B [a] rec/checks (kw [] ::permission) (st [] #{1})) 'B) {::a 1})]
      (is (true? (rec/proves? v ::permission)) "no check carries the concern")
      (is (= #{} (rec/checks-of ::permission (class v)))))))

(deftest a-flag-the-macros-do-not-know-is-refused
  (is (= "::nope on never names no concern that rec/defconcern defines"
         (refusal '(rec/defchecks b [a] rec/checks (never [] ::nope true)))))
  (is (= "unknown flag :permission on never: a clause's flags are :override and concerns"
         (refusal '(rec/defchecks b [a] rec/checks (never [] :permission true)))))
  (is (= "a clause's flags are keywords and concerns' symbols: #{\"x\"} on never"
         (refusal '(rec/defchecks b [a] rec/checks (never [] #{"x"} true)))))
  (is (= (str ":override on never: a bundle's check replaces no check; :override is for a"
              " clause of a type that replaces a check of a bound bundle")
         (refusal '(rec/defchecks b [a] rec/checks (never [] :override true))))))

(defn- not-a-concern [s nm]
  (str s " on " nm " is not a concern: a symbol after a clause's waits names a concern that"
       " rec/defconcern defines"))

(deftest a-concern-is-named-by-its-symbol
  (testing "alone, before the body or before a docstring"
    (let [v ((make '(rec/defproven-in Y [a] rec/checks
                                      (never [] permission (= a :never))
                                      (dnever [] audit "never passes" (= a :never)))
                   'Y)
             {::a 1})]
      (is (= #{::never} (rec/checks-of ::permission (class v))))
      (is (= #{::dnever} (rec/checks-of ::audit (class v))))
      (is (false? (rec/proves? v ::audit)))))
  (testing "qualified by an alias, and in a set with a keyword"
    (let [v ((make '(rec/defproven-in Z [a] rec/checks
                                      (never [] #{recognitum.flag-place-test/permission ::audit} (= a :never)))
                   'Z)
             {::a 1})]
      (is (= #{::never} (rec/checks-of ::audit (class v)) (rec/checks-of ::permission (class v))))))
  (testing "on a bundle's check"
    (is (nil? (refusal '(rec/defchecks sym-checks [a] rec/checks (snever [] permission "never" (= a :never))))))
    (is (= #{::permission} (:concerns @(resolve 'recognitum.flag-place-test/snever))))))

(deftest a-symbol-that-names-no-concern-is-refused
  (testing "a name that resolves to nothing, a var that is no concern, a field"
    (is (= (not-a-concern 'permision 'never)
           (refusal '(rec/defproven T [a] rec/checks (never [] permision (= a :never))))))
    (is (= (not-a-concern 'x-positive 'never)
           (refusal '(rec/defproven T [a] rec/checks (never [] x-positive (= a :never))))))
    (is (= (not-a-concern 'a 'never)
           (refusal '(rec/defproven T [a] rec/checks (never [] a "never passes" (= a :never))))))
    (is (= (not-a-concern 'refusal 'never)
           (refusal '(rec/defchecks b [a] rec/checks (never [] refusal (= a :never)))))))
  (testing "in a set"
    (is (= (not-a-concern 'nope 'never)
           (refusal '(rec/defproven T [a] rec/checks (never [] #{permission nope} (= a :never))))))))

(deftest a-concern-or-a-symbol-alone-after-the-waits-is-the-body
  (doseq [form '[(rec/defproven A1 [a] rec/checks (kw [] ::permission))
                 (rec/defproven A1 [a] rec/checks (kw [] permission))]]
    (testing (pr-str (last form))
      (let [mk (make form 'A1)
            thrown (try (mk {::a 1}) nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= #{::kw} (set (keys (:failed (ex-data thrown)))))
            "the check fails: its body returns the concern, which is not true")
        (is (= #{} (rec/checks-of ::permission (ns-resolve 'recognitum.flag-place-test 'A1))))))))

(deftest a-concern-symbol-on-an-input-clause-is-refused
  (is (= (str "permission on input clause x of positives" input-remedy)
         (refusal '(rec/defproven T [a] positives (x [] permission a) rec/checks (ok [] true)))))
  (testing "any other symbol there is the body"
    (is (nil? (refusal '(rec/defproven T [a b] positives (x [] b a) rec/checks (ok [] true)))))))
