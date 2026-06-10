;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09216.smt2
;; Mutations:  range_shrink_hi, range_shrink_lo, bound_upper_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, range_shrink_lo, bound_upper_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "(") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re ")") ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}"))
      (re.++ (str.to_re "(") ((_ re.loop 3 4) (re.range "0" "9")) (str.to_re ")") ((_ re.loop 3 3) (re.range "1" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "8")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
