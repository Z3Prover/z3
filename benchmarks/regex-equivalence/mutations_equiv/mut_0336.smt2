;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance13747.smt2
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
      (re.union (re.++ (re.* (re.range "0" "9")) (str.to_re " ") (re.* (re.range "0" "9")) ((_ re.loop 1 1) (str.to_re "/")) (re.* (re.range "0" "9"))) (re.++ (re.* (re.range "0" "9")) (str.to_re "\u{a}")))
      (re.union (re.++ (re.inter (re.* (re.range "0" "9")) (re.comp (re.++ re.all (str.to_re "@") re.all))) (str.to_re " ") (re.* (re.range "0" "9")) ((_ re.loop 1 1) (str.to_re "/")) (re.* (re.range "0" "9"))) (re.++ (re.* (re.range "0" "9")) (str.to_re "\u{a}"))))))

(check-sat)
(exit)
