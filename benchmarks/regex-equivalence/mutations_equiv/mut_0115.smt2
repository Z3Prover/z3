;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01423.smt2
;; Mutations:  intersect_no_at_sign
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_at_sign)
(assert
  (not
    (=
      (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".pkp/i\u{a}"))
      (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (re.inter (str.to_re ".pkp/i\u{a}") (re.comp (re.++ re.all (str.to_re "@") re.all)))))))

(check-sat)
(exit)
