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
  (testing "a keyword or set alone after the waits that is no concern is the body"
    (let [v ((make '(rec/defproven-in B [a] rec/checks (kw [] ::nope) (st [] #{1})) 'B) {::a 1})]
      (is (= #{::kw ::st} (set (keys (:failed (rec/check v rec/every))))))
      (is (= #{} (rec/checks-of ::permission (class v))))
      (testing "no check carries the concern, so a seal by it is refused and proves? by it is false"
        (is (= :recognitum/selects-nothing
               (try (rec/seal v ::permission) nil
                    (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))))
        (is (false? (rec/proves? v ::permission)))))))

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

(deftest a-constant-alone-after-the-waits-that-is-no-concern-is-the-body
  (doseq [form '[(rec/defproven A1 [a] rec/checks (kw [] ::q))
                 (rec/defproven A1 [a] rec/checks (kw [] :permission))
                 (rec/defproven A1 [a] rec/checks (kw [] "Doc." #{1 :q}))]]
    (testing (pr-str (last form))
      (let [mk (make form 'A1)
            thrown (try (mk {::a 1}) nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= #{::kw} (set (keys (:failed (ex-data thrown)))))
            "the check fails: its body returns the constant, which is not true")))))

(deftest a-concern-symbol-on-an-input-clause-is-refused
  (is (= (str "permission on input clause x of positives" input-remedy)
         (refusal '(rec/defproven T [a] positives (x [] permission a) rec/checks (ok [] true)))))
  (testing "any other symbol there is the body"
    (is (nil? (refusal '(rec/defproven T [a b] positives (x [] b a) rec/checks (ok [] true)))))))

(defn- defining
  "What `(f)` answers, where `f` evaluates a definition, or `:refused` where a macro refuses the
  definition."
  [f]
  (try (f)
       (catch clojure.lang.Compiler$CompilerException e
         (if (= :recognitum/refused (:error (ex-data (ex-cause e)))) :refused (throw e)))))

(defn- unless-refused
  "`(f x)`, or `:refused` where `x` is."
  [x f]
  (if (= :refused x) x (f x)))

(deftest a-concern-written-after-the-first-flag-position-is-not-dropped-test
  (let [maker (fn [tname & sections]
                (defining #(make (list* 'rec/defproven-in tname '[a] sections) tname)))
        selected (fn [mk concern] (unless-refused mk #(rec/checks-of concern (class (% {::a -1})))))]
    (testing "the concern, then the docstring: the check carries the concern"
      (let [mk (maker 'Documented 'rec/checks '(allowed [] permission "The actor may." (pos? a)))
            v (mk {::a -1})]
        (is (= #{::allowed} (selected mk permission)))
        (is (= :recognitum/check-failed
               (try (rec/seal v permission) nil
                    (catch clojure.lang.ExceptionInfo e (:error (ex-data e))))))
        (is (false? (rec/proves? v permission)))))
    (testing "a definition that a macro refuses"
      (is (= :refused (maker 'Unknown 'rec/checks '(allowed [] ::nope "The actor may." (pos? a))))))
    (testing "a concern written later is carried, or the definition is refused"
      (doseq [[what tname concern clause]
              [["a symbol after the docstring" 'DocSymbol permission
                '(allowed [] "The actor may." permission (pos? a))]
               ["a keyword after the docstring" 'DocKeyword permission
                '(allowed [] "The actor may." ::permission (pos? a))]
               ["a set after the docstring" 'DocSet permission
                '(allowed [] "The actor may." #{permission audit} (pos? a))]
               ["a symbol after a symbol" 'TwoSymbols audit
                '(allowed [] permission audit (pos? a))]
               ["a symbol after a keyword" 'KeywordSymbol audit
                '(allowed [] ::permission audit (pos? a))]]]
        (testing what
          (is (contains? #{:refused #{::allowed}} (selected (maker tname 'rec/checks clause) concern)))))
      (testing "a symbol after :override"
        (is (contains? #{:refused #{::x-positive}}
                       (selected (maker 'OverrideSymbol 'positives '(x [] a)
                                        'rec/checks
                                        '(recognitum.flag-place-test/x-positive [] :override audit (pos? a)))
                                 audit)))))
    (testing "accepted, the definition gives no value that proves the concern while the check fails"
      (let [mk (maker 'Unproven 'rec/checks '(allowed [] "The actor may." permission (pos? a)))]
        (is (contains? #{:refused #{::allowed}}
                       (unless-refused mk #(set (keys (:failed (rec/check (% {::a -1}) rec/every))))))
            "the check fails on the value")
        (is (contains? #{:refused false} (unless-refused mk #(rec/proves? (% {::a -1}) permission))))))))

(deftest a-referred-concern-named-by-keyword-is-carried-or-refused-test
  (let [scratch 'recognitum.flag-place-test.referring
        n (create-ns scratch)
        id #(keyword (str scratch) %)
        defined (fn [text] (defining #(binding [*ns* n] (load-string text))))
        failing (fn [T] (into (rec/draft T) {(id "a") -1}))]
    (try
      (binding [*ns* n]
        (refer-clojure)
        (alias 'rec 'recognitum.core)
        (refer 'recognitum.flag-place-test :only '[permission]))
      (testing "named by its symbol where it is referred, the concern is carried"
        (let [T (defined "(rec/defproven BySymbol [a] rec/checks (c [] permission (pos? a)))")]
          (is (= #{(id "c")} (rec/checks-of permission T)))
          (is (false? (rec/proves? (failing T) permission)))))
      (testing "a definition that a macro refuses"
        (is (= :refused (defined "(rec/defproven NoConcern [a] rec/checks (c [] ::nope (pos? a)))"))))
      (testing "named by ::permission where it is referred, it is carried, or the definition is refused"
        (let [T (defined "(rec/defproven ByKeyword [a] rec/checks (c [] ::permission (pos? a)))")]
          (is (contains? #{:refused #{(id "c")}} (unless-refused T #(rec/checks-of permission %))))
          (testing "accepted, a draft on which the check fails does not prove the concern"
            (is (contains? #{:refused #{(id "c")}}
                           (unless-refused T #(set (keys (:failed (rec/check (failing %) rec/every))))))
                "the check fails on the draft")
            (is (contains? #{:refused false} (unless-refused T #(rec/proves? (failing %) permission)))))))
      (finally (remove-ns scratch)))))

(defn- out-of-place
  "The refusal of `found`, written at `place` in a clause, with `head` the clause's head as it
  should be written."
  [found place head]
  (str found ", written " place ", " (if (re-find #" and " found) "are" "is")
       " in the body, where no flag is read: a clause's flags follow its waits, before its"
       " docstring, and several go in one set, as in " head))

(deftest a-flag-out-of-its-place-is-refused
  (testing "after the docstring: a symbol, a keyword, a set"
    (is (= (out-of-place "permission" "after the docstring of allowed" "(allowed [] permission \"...\" ...)")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] "The actor may." permission (pos? a))))))
    (is (= (out-of-place "::permission" "after the docstring of allowed" "(allowed [] ::permission \"...\" ...)")
           (refusal '(rec/defproven-in T [a] rec/checks (allowed [] "The actor may." ::permission (pos? a))))))
    (is (= (out-of-place "#{audit permission}" "after the docstring of allowed"
                         "(allowed [] #{audit permission} \"...\" ...)")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] "The actor may." #{permission audit} (pos? a)))))))
  (testing "a second flag outside a set, the flags in place joined with it"
    (is (= (out-of-place "audit" "after permission on allowed" "(allowed [] #{audit permission} ...)")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] permission audit (pos? a))))))
    (is (= (out-of-place "audit and :foo" "after the docstring of allowed"
                         "(allowed [] #{::permission :foo audit} \"...\" ...)")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] #{::permission} "Doc." audit :foo (pos? a)))))))
  (testing "after :override"
    (is (= (out-of-place "audit" "after :override on recognitum.flag-place-test/x-positive"
                         "(recognitum.flag-place-test/x-positive [] #{:override audit} ...)")
           (refusal '(rec/defproven T [a] positives (x [] a)
                                    rec/checks (recognitum.flag-place-test/x-positive [] :override audit (pos? a)))))))
  (testing "after other forms of the body"
    (is (= (out-of-place "audit" "after other forms in the body of allowed" "(allowed [] audit ...)")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] (pos? a) audit (pos? a)))))))
  (testing "in a bundle's check"
    (is (= (out-of-place "permission" "after the docstring of allowed" "(allowed [] permission \"...\" ...)")
           (refusal '(rec/defchecks misplaced [a] rec/checks (allowed [] "Doc." permission (pos? a)))))))
  (testing "in an input clause"
    (is (= (str "::permission, written after the docstring of input clause x of positives, is in the body,"
                " where no flag is read" input-remedy)
           (refusal '(rec/defproven T [a] positives (x [] "Doc." ::permission a) rec/checks (ok [] true)))))))

(deftest a-flag-form-as-the-last-of-several-forms-is-not-refused
  (doseq [clause '[(alone [] (pos? a) permission)
                   (alone [] audit "Doc." (pos? a) ::permission)]]
    (testing (pr-str clause)
      (is (nil? (refusal (list 'rec/defproven-in 'Last '[a] 'rec/checks clause)))))))

(deftest a-keyword-flag-is-the-concern-s-own-id
  (let [scratch 'recognitum.flag-place-test.keyword-ids
        n (create-ns scratch)
        refused (fn [text] (try (binding [*ns* n] (load-string text)) nil
                                (catch clojure.lang.Compiler$CompilerException e (:message (ex-data (ex-cause e))))))
        not-the-id (fn [shown where sym]
                     (str shown " on c is not the id of a concern: permission " where " is the concern"
                          " recognitum.flag-place-test/permission, whose id is"
                          " :recognitum.flag-place-test/permission. Write " sym
                          " or :recognitum.flag-place-test/permission"))]
    (try
      (binding [*ns* n]
        (refer-clojure)
        (alias 'rec 'recognitum.core)
        (alias 'fp 'recognitum.flag-place-test)
        (refer 'recognitum.flag-place-test :only '[permission x-positive]))
      (testing "::name of a referred concern, alone or in a set, in a type or a bundle"
        (is (= (not-the-id "::permission" "here" "permission")
               (refused "(rec/defproven K [a] rec/checks (c [] ::permission (pos? a)))")))
        (is (= (not-the-id "::permission" "here" "permission")
               (refused "(rec/defproven K [a] rec/checks (c [] #{::permission ::fp/audit} (pos? a)))")))
        (is (= (not-the-id "::permission" "here" "permission")
               (refused "(rec/defchecks bk [a] rec/checks (c [] ::permission (pos? a)))"))))
      (testing "the keyword of another namespace that refers the concern"
        (is (= (not-the-id ":recognitum.flag-place-test.keyword-ids/permission"
                           "in recognitum.flag-place-test.keyword-ids" "permission")
               (refusal '(rec/defproven K [a] rec/checks
                                        (c [] :recognitum.flag-place-test.keyword-ids/permission (pos? a)))))))
      (testing "::name of a referred var that is no concern"
        (is (= "::x-positive on c names no concern that rec/defconcern defines"
               (refused "(rec/defproven K [a] rec/checks (c [] ::x-positive (pos? a)))"))))
      (testing "the right spellings are accepted"
        (is (nil? (refused "(rec/defproven K [a] rec/checks (c [] #{permission ::fp/permission :recognitum.flag-place-test/audit} (pos? a)))"))))
      (finally (remove-ns scratch)))))

(defn- no-body
  "The refusal of `found`, the whole body of check `nm`, with `head` the clause as it should be
  written, up to its body."
  [found nm head]
  (str found ", the whole body of " nm ", is a flag, so " nm " has flags and no body: a concern after"
       " a clause's waits is one of its flags, and the body follows the flags, as in " head " body)"))

(deftest a-check-whose-whole-body-is-a-concern-is-refused
  (testing "a symbol, a keyword, a set; after a docstring; after a flag"
    (is (= (no-body "permission" "allowed" "(allowed [] permission")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] permission)))))
    (is (= (no-body "::permission" "allowed" "(allowed [] ::permission \"...\"")
           (refusal '(rec/defproven-in T [a] rec/checks (allowed [] "The actor may." ::permission)))))
    (is (= (no-body "#{1 permission}" "allowed" "(allowed [] #{1 permission}")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] #{permission 1})))))
    (is (= (no-body "audit" "allowed" "(allowed [] #{audit permission}")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] permission audit))))))
  (testing "after :override, and in a bundle's check"
    (is (= (no-body "audit" "recognitum.flag-place-test/x-positive"
                    "(recognitum.flag-place-test/x-positive [] #{:override audit}")
           (refusal '(rec/defproven T [a] positives (x [] a)
                                    rec/checks (recognitum.flag-place-test/x-positive [] :override audit)))))
    (is (= (no-body "permission" "allowed" "(allowed [] permission \"...\"")
           (refusal '(rec/defchecks alone-checks [a] rec/checks (allowed [] "Doc." permission))))))
  (testing "an input clause's one form is the input's value"
    (is (nil? (refusal '(rec/defproven T [a] positives (x [] permission) rec/checks (ok [] true)))))))

(deftest a-check-whose-whole-body-is-a-referred-concern-s-keyword-is-refused
  (let [scratch 'recognitum.flag-place-test.whole-body
        n (create-ns scratch)
        refused (fn [text] (try (binding [*ns* n] (load-string text)) nil
                                (catch clojure.lang.Compiler$CompilerException e (:message (ex-data (ex-cause e))))))
        not-the-id (str "::permission on c is not the id of a concern: permission here is the concern"
                        " recognitum.flag-place-test/permission, whose id is"
                        " :recognitum.flag-place-test/permission. Write permission"
                        " or :recognitum.flag-place-test/permission")]
    (try
      (binding [*ns* n]
        (refer-clojure)
        (alias 'rec 'recognitum.core)
        (refer 'recognitum.flag-place-test :only '[permission x-positive]))
      (is (= not-the-id (refused "(rec/defproven K [a] rec/checks (c [] ::permission))")))
      (is (= not-the-id (refused "(rec/defproven K [a] rec/checks (c [] \"Doc.\" #{::permission 1}))")))
      (testing "a keyword whose name resolves to a var that is no concern is the body"
        (is (nil? (refused "(rec/defproven K [a] rec/checks (c [] ::x-positive))"))))
      (finally (remove-ns scratch)))))

(deftest a-one-element-set-as-a-check-s-whole-body-is-refused
  (testing "a set holding the concern's symbol or its id"
    (is (= (no-body "#{permission}" "allowed" "(allowed [] permission")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] #{permission})))))
    (is (= (no-body "#{::permission}" "allowed" "(allowed [] ::permission")
           (refusal '(rec/defproven T [a] rec/checks (allowed [] #{::permission}))))))
  (testing "a set holding ::name of a concern the namespace refers"
    (let [scratch 'recognitum.flag-place-test.one-element-set
          n (create-ns scratch)]
      (try
        (binding [*ns* n]
          (refer-clojure)
          (alias 'rec 'recognitum.core)
          (refer 'recognitum.flag-place-test :only '[permission]))
        (is (= (str "::permission on c is not the id of a concern: permission here is the concern"
                    " recognitum.flag-place-test/permission, whose id is"
                    " :recognitum.flag-place-test/permission. Write permission"
                    " or :recognitum.flag-place-test/permission")
               (try (binding [*ns* n] (load-string "(rec/defproven K [a] rec/checks (c [] #{::permission}))")) nil
                    (catch clojure.lang.Compiler$CompilerException e (:message (ex-data (ex-cause e)))))))
        (finally (remove-ns scratch))))))

(def ^:private statements (atom 0))

(deftest a-body-of-several-forms-runs-each-and-answers-the-last
  (let [mk (make '(rec/defproven-in Several [a] rec/checks
                                    (counted [] (swap! statements inc) (pos? a)))
                 'Several)
        failed (fn [v] (set (keys (:failed (rec/check v rec/every)))))]
    (reset! statements 0)
    (is (= #{} (failed (mk {::a 1}))) "the last form's true passes the check")
    (is (= 1 @statements) "the first form ran")
    (is (= #{::counted} (failed (mk {::a -1}))) "the last form's false fails the check")
    (is (= 2 @statements))))
