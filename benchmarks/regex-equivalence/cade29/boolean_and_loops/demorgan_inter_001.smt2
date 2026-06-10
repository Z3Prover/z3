;; Category : boolean_and_loops
;; Source   : Boolean algebra laws
;; De Morgan: ¬(A∩B) ≡ ¬A∪¬B [digit_alpha]
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.comp (re.inter (re.range "0" "9") (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.union (re.comp (re.range "0" "9")) (re.comp (re.union (re.range "a" "z") (re.range "A" "Z")))))))

(check-sat)
(exit)
