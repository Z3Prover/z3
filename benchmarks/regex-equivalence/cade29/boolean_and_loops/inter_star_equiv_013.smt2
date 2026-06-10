;; Category : boolean_and_loops
;; Source   : Boolean+star interaction
;; (A∩B)* ≡ A*∩B* when A⊆B (digit ⊆ alnum)
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.* (re.inter (re.range "0" "9") (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")))) (re.inter (re.* (re.range "0" "9")) (re.* (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")))))))

(check-sat)
(exit)
