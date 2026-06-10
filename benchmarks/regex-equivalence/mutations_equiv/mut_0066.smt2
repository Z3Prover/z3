;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance04391.smt2
;; Mutations:  intersect_min_len_5
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_min_len_5)
(assert
  (not
    (=
      (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".pfa/i\u{a}"))
      (re.++ (str.to_re "/filename=") (re.inter (re.* (re.comp (str.to_re "\u{a}"))) (re.++ ((_ re.loop 5 5) re.allchar) re.all)) (str.to_re ".pfa/i\u{a}")))))

(check-sat)
(exit)
