;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance00545.smt2
;; Mutations:  range_shrink_lo, range_shrink_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, range_shrink_hi)
(assert
  (not
    (=
      (re.++ (re.union (re.range "1" "9") (re.++ (str.to_re "1") (re.range "0" "2"))) (str.to_re "\u{a}"))
      (re.++ (re.union (re.range "1" "8") (re.++ (str.to_re "1") (re.range "1" "2"))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
