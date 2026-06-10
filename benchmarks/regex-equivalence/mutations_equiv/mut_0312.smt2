;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance12619.smt2
;; Mutations:  range_shrink_hi, bound_upper_inc, range_expand_hi
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (range_shrink_hi, bound_upper_inc, range_expand_hi)
(assert
  (not
    (=
      (re.union (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (re.* (re.++ (str.to_re ",") ((_ re.loop 3 3) (re.range "0" "9"))))) (re.++ ((_ re.loop 1 16) (re.range "0" "9")) (str.to_re "\u{a}")))
      (re.union (re.++ ((_ re.loop 1 3) (re.range "0" "9")) (re.* (re.++ (str.to_re ",") ((_ re.loop 3 3) (re.range "0" ":"))))) (re.++ ((_ re.loop 1 17) (re.range "0" "8")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
