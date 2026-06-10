;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01941.smt2
;; Mutations:  intersect_no_dot_dot
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_dot_dot)
(assert
  (not
    (=
      (re.++ (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))) (str.to_re "\u{a}"))
      (re.++ (re.inter (re.* (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.comp (re.++ re.all (str.to_re "..") re.all))) (str.to_re "\u{a}")))))

(check-sat)
(exit)
