;; Category : boolean_and_loops
;; Source   : Regular expression algebra
;; Distributivity: A·(B∪C) ≡ A·B∪A·C
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.++ (re.range "0" "9") (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.comp (re.union (re.++ (re.range "0" "9") (re.range "a" "z")) (re.++ (re.range "0" "9") (re.range "A" "Z")))))
      (re.inter (re.comp (re.++ (re.range "0" "9") (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.union (re.++ (re.range "0" "9") (re.range "a" "z")) (re.++ (re.range "0" "9") (re.range "A" "Z")))))))

(check-sat)
(exit)
