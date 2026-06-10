;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03580.smt2
;; Mutations:  star_to_plus
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (star_to_plus)
(assert
  (not
    (=
      (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\u{a}"))) (str.to_re ".cpe/i\u{a}"))
      (re.++ (str.to_re "/filename=") (re.+ (re.comp (str.to_re "\u{a}"))) (str.to_re ".cpe/i\u{a}")))))

(check-sat)
(exit)
