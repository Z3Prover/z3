;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13587.smt2
;; Mutations:  range_shrink_lo, range_shrink_hi, bound_upper_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, range_shrink_hi, bound_upper_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "01") ((_ re.loop 1 1) (re.range "0" "2")) ((_ re.loop 8 8) (re.range "0" "9")) (str.to_re "\u{a}"))
      (re.++ (str.to_re "01") ((_ re.loop 1 2) (re.range "0" "1")) ((_ re.loop 8 8) (re.range "1" "9")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
