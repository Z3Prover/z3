;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01708.smt2
;; Mutations:  range_shrink_lo, bound_lower_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, bound_lower_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "//b/shoe/") ((_ re.loop 3 5) (re.range "0" "9")) (str.to_re "/U\u{a}"))
      (re.++ (str.to_re "//b/shoe/") ((_ re.loop 2 5) (re.range "1" "9")) (str.to_re "/U\u{a}")))))

(check-sat)
(exit)
