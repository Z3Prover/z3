;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03806.smt2
;; Mutations:  literal_char_inc
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
;; R2: mutated (literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "//java") (re.union (str.to_re "rh") (str.to_re "db")) (str.to_re ".php/U\u{a}")) (re.comp (re.++ (str.to_re "//java") (re.union (str.to_re "ri") (str.to_re "db")) (str.to_re ".php/U\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "//java") (re.union (str.to_re "rh") (str.to_re "db")) (str.to_re ".php/U\u{a}"))) (re.++ (str.to_re "//java") (re.union (str.to_re "ri") (str.to_re "db")) (str.to_re ".php/U\u{a}"))))))

(check-sat)
(exit)
