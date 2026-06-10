;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02352.smt2
;; Mutations:  literal_char_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_dec)
(assert
  (not
    (=
      (re.++ ((_ re.loop 0 2) (str.to_re ".")) (re.union (str.to_re "/") (str.to_re "\u{5c}")) (str.to_re "\u{a}"))
      (re.++ ((_ re.loop 0 2) (str.to_re ".")) (re.union (str.to_re ".") (str.to_re "\u{5c}")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
