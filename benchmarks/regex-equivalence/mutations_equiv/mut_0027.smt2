;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01587.smt2
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
      (re.++ (str.to_re "\u{a}") ((_ re.loop 9 9) (re.range "0" "9")) (re.union (str.to_re "V") (str.to_re "|") (str.to_re "v") (str.to_re "x") (str.to_re "X")))
      (re.++ (str.to_re "\u{a}") ((_ re.loop 9 9) (re.range "0" "9")) (re.inter (str.to_re "V") (str.to_re "|") (str.to_re "v") (str.to_re "x") (str.to_re "X"))))))

(check-sat)
(exit)
