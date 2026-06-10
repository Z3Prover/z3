;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance05974.smt2
;; Mutations:  bound_lower_dec
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (bound_lower_dec)
(assert
  (not
    (=
      (re.++ (str.to_re "//lists/") ((_ re.loop 20 20) (re.range "0" "9")) (str.to_re "/U\u{a}"))
      (re.++ (str.to_re "//lists/") ((_ re.loop 19 20) (re.range "0" "9")) (str.to_re "/U\u{a}")))))

(check-sat)
(exit)
