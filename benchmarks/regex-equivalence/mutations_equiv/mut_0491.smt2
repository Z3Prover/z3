;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12998.smt2
;; Mutations:  range_shrink_hi, range_shrink_lo, plus_to_star
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, range_shrink_lo, plus_to_star)
(assert
  (not
    (=
      (re.++ (re.+ (re.union (re.range "A" "Z") (re.range "a" "z") (re.range "0" "9") (str.to_re "_"))) (str.to_re "\u{a}"))
      (re.++ (re.* (re.union (re.range "B" "Z") (re.range "a" "z") (re.range "0" "8") (str.to_re "_"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
