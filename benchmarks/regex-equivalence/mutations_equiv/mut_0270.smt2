;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance07035.smt2
;; Mutations:  bound_upper_inc, range_expand_hi, bound_lower_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (bound_upper_inc, range_expand_hi, bound_lower_dec)
(assert
  (not
    (=
      (re.union (re.++ (re.+ (re.++ ((_ re.loop 12 12) (re.range "0" "9")) (str.to_re ","))) ((_ re.loop 12 12) (re.range "0" "9"))) (re.++ ((_ re.loop 12 12) (re.range "0" "9")) (str.to_re "\u{a}")))
      (re.union (re.++ (re.+ (re.++ ((_ re.loop 11 12) (re.range "0" ":")) (str.to_re ","))) ((_ re.loop 12 12) (re.range "0" "9"))) (re.++ ((_ re.loop 12 13) (re.range "0" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
