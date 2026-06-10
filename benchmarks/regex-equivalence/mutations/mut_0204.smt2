;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance15175.smt2
;; Mutations:  opt_to_required
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

;; R1: original
;; R2: mutated (opt_to_required)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (re.* (re.union (str.to_re "]") (str.to_re "\u{22}"))) (re.* (re.comp (str.to_re "["))) (str.to_re "[/url]\u{a}[url") (re.opt (str.to_re "=")) (re.opt (str.to_re "\u{22}")) (re.opt (str.to_re "\u{22}")) (str.to_re "]")) (re.comp (re.++ (re.* (re.union (str.to_re "]") (str.to_re "\u{22}"))) (re.* (re.comp (str.to_re "["))) (str.to_re "[/url]\u{a}[url") str.to_re "=") (re.opt (str.to_re "\u{22}")) (re.opt (str.to_re "\u{22}")) (str.to_re "]")))) (re.inter (re.comp (re.++ (re.* (re.union (str.to_re "]") (str.to_re "\u{22}"))) (re.* (re.comp (str.to_re "["))) (str.to_re "[/url]\u{a}[url") (re.opt (str.to_re "=")) (re.opt (str.to_re "\u{22}")) (re.opt (str.to_re "\u{22}")) (str.to_re "]"))) (re.++ (re.* (re.union (str.to_re "]") (str.to_re "\u{22}"))) (re.* (re.comp (str.to_re "["))) (str.to_re "[/url]\u{a}[url") str.to_re "=") (re.opt (str.to_re "\u{22}")) (re.opt (str.to_re "\u{22}")) (str.to_re "]"))))))

(check-sat)
(exit)
