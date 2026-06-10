;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance03674.smt2
;; Mutations:  union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (union_to_inter)
(assert
  (not
    (=
      (re.++ (str.to_re "/.f4v") (re.union (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}"))
      (re.++ (str.to_re "/.f4v") (re.inter (str.to_re "?") (str.to_re "\u{5c}") (str.to_re "/")) (str.to_re "/smiU\u{a}")))))

(check-sat)
(exit)
