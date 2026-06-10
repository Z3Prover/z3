;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance06454.smt2
;; Mutations:  opt_to_required, union_to_inter
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (opt_to_required, union_to_inter)
(assert
  (not
    (=
      (re.++ (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.opt (re.++ (str.to_re " ") (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))))) (str.to_re "\u{a}"))
      (re.++ (re.* (re.inter (re.range "a" "z") (re.range "A" "Z"))) re.++ (str.to_re " ") (re.* (re.union (re.range "a" "z") (re.range "A" "Z")))))))

(check-sat)
(exit)
