;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance01144.smt2
;; Mutations:  intersect_no_dot_dot, intersect_no_upper2
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (intersect_no_dot_dot, intersect_no_upper2)
(assert
  (not
    (=
      (re.++ (str.to_re "\u{a}") ((_ re.loop 1 1) (re.range "2" "9")) ((_ re.loop 2 2) (re.range "0" "9")) ((_ re.loop 3 3) (re.range "0" "9")) ((_ re.loop 4 4) (re.range "0" "9")))
      (re.++ (str.to_re "\u{a}") (re.inter ((_ re.loop 1 1) (re.range "2" "9")) (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) ((_ re.loop 2 2) (re.range "0" "9")) (re.inter ((_ re.loop 3 3) (re.range "0" "9")) (re.comp (re.++ re.all (str.to_re "..") re.all))) ((_ re.loop 4 4) (re.range "0" "9"))))))

(check-sat)
(exit)
