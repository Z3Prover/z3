;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance08950.smt2
;; Mutations:  range_shrink_lo, bound_lower_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, bound_lower_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "/\u{d}\u{a}\u{d}\u{a}session:") ((_ re.loop 1 7) (re.range "0" "9")) (str.to_re "/\u{a}"))
      (re.++ (str.to_re "/\u{d}\u{a}\u{d}\u{a}session:") ((_ re.loop 2 7) (re.range "1" "9")) (str.to_re "/\u{a}")))))

(check-sat)
(exit)
