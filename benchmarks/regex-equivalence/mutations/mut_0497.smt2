;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11469.smt2
;; Mutations:  range_expand_hi, bound_lower_dec
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
;; R2: mutated (range_expand_hi, bound_lower_dec)
(assert
  (str.in_re x
    (re.union (re.inter (re.union (re.++ (re.* ((_ re.loop 5 5) (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9"))) (re.++ ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "\u{a}"))) (re.comp (re.union (re.++ (re.* ((_ re.loop 5 5) (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 3 4) (re.range "0" "9"))) (re.++ ((_ re.loop 5 5) (re.range "0" ":")) (str.to_re "\u{a}"))))) (re.inter (re.comp (re.union (re.++ (re.* ((_ re.loop 5 5) (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9"))) (re.++ ((_ re.loop 5 5) (re.range "0" "9")) (str.to_re "\u{a}")))) (re.union (re.++ (re.* ((_ re.loop 5 5) (re.range "0" "9"))) (str.to_re "-") ((_ re.loop 3 4) (re.range "0" "9"))) (re.++ ((_ re.loop 5 5) (re.range "0" ":")) (str.to_re "\u{a}")))))))

(check-sat)
(exit)
