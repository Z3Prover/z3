;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance09651.smt2
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
      (re.union (re.++ (re.opt (re.++ (str.to_re "ES") (re.opt (str.to_re "-")))) (re.union (re.range "0" "9") (re.range "A" "Z")) ((_ re.loop 7 7) (re.range "0" "9")) (re.range "A" "Z")) (re.++ (str.to_re "\u{a}") (re.range "A" "Z") ((_ re.loop 7 7) (re.range "0" "9")) (re.union (re.range "0" "9") (re.range "A" "Z"))))
      (re.union (re.++ (re.opt (re.++ (str.to_re "ES") (re.opt (str.to_re "-")))) (re.inter (re.union (re.range "0" "9") (re.range "A" "Z")) (re.comp (re.++ re.all (str.to_re "@") re.all))) ((_ re.loop 7 7) (re.range "0" "9")) (re.range "A" "Z")) (re.++ (str.to_re "\u{a}") (re.range "A" "Z") ((_ re.loop 7 7) (re.range "0" "9")) (re.union (re.range "0" "9") (re.range "A" "Z")))))))

(check-sat)
(exit)
