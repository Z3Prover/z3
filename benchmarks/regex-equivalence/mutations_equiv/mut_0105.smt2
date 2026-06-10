;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04496.smt2
;; Mutations:  bound_upper_inc, bound_lower_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (bound_upper_inc, bound_lower_dec)
(assert
  (not
    (=
      (re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 4) (re.range "0" "9")) (str.to_re "\u{a}"))
      (re.++ ((_ re.loop 2 3) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 2 2) (re.range "0" "9")) (str.to_re "-") ((_ re.loop 4 5) (re.range "0" "9")) (str.to_re "\u{a}")))))

(check-sat)
(exit)
