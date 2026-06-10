;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance07187.smt2
;; Mutations:  range_shrink_lo, bound_upper_inc, intersect_no_at_sign
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_lo, bound_upper_inc, intersect_no_at_sign)
(assert
  (not
    (=
      (re.++ (str.to_re "//setup/") ((_ re.loop 50 50) (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "!") (str.to_re "-"))) (str.to_re "/Ui\u{a}"))
      (re.++ (re.inter (str.to_re "//setup/") (re.comp (re.++ re.all (str.to_re "@") re.all))) ((_ re.loop 50 51) (re.union (re.range "b" "z") (re.range "0" "9") (str.to_re "!") (str.to_re "-"))) (str.to_re "/Ui\u{a}")))))

(check-sat)
(exit)
