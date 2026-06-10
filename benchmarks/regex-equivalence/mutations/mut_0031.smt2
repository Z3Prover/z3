;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04792.smt2
;; Mutations:  literal_char_dec
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
;; R2: mutated (literal_char_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "/*") (re.* re.allchar) (str.to_re "*/\u{a}")) (re.comp (re.++ (str.to_re "/)") (re.* re.allchar) (str.to_re "*/\u{a}")))) (re.inter (re.comp (re.++ (str.to_re "/*") (re.* re.allchar) (str.to_re "*/\u{a}"))) (re.++ (str.to_re "/)") (re.* re.allchar) (str.to_re "*/\u{a}"))))))

(check-sat)
(exit)
