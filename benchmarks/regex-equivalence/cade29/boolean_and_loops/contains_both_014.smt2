;; Category : boolean_and_loops
;; Source   : Boolean+concat interaction
;; .*a.* ∩ .*b.* ≡ .*a.*b.* ∪ .*b.*a.*
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.++ (re.* re.allchar) (str.to_re "a") (re.* re.allchar)) (re.++ (re.* re.allchar) (str.to_re "b") (re.* re.allchar))) (re.union (re.++ (re.* re.allchar) (str.to_re "a") (re.* re.allchar) (str.to_re "b") (re.* re.allchar)) (re.++ (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "a") (re.* re.allchar))))))

(check-sat)
(exit)
