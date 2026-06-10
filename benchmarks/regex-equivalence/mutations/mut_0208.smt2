;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance02432.smt2
;; Mutations:  range_expand_hi, range_shrink_hi, bound_lower_dec
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
;; R2: mutated (range_expand_hi, range_shrink_hi, bound_lower_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "\u{a}") ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 3 3) (re.range "0" "9"))) (re.comp (re.++ (str.to_re "\u{a}") ((_ re.loop 4 5) (re.range "0" "8")) (str.to_re "-") ((_ re.loop 3 3) (re.range "0" ":"))))) (re.inter (re.comp (re.++ (str.to_re "\u{a}") ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 3 3) (re.range "0" "9")))) (re.++ (str.to_re "\u{a}") ((_ re.loop 4 5) (re.range "0" "8")) (str.to_re "-") ((_ re.loop 3 3) (re.range "0" ":")))))))

(check-sat)
(exit)
