;; Category : parametric
;; Source   : CADE 29 b-param style (containment)
;; At-least-3-a's: (.*a){3}.* ≡ ¬(at-most-2-a's)
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ ((_ re.loop 3 3) (re.++ (re.* re.allchar) (str.to_re "a"))) (re.* re.allchar)) (re.comp (re.union (re.union (re.* (re.inter re.allchar (re.comp (str.to_re "a")))) (re.++ (re.* (re.inter re.allchar (re.comp (str.to_re "a")))) ((_ re.loop 1 1) (re.++ (str.to_re "a") (re.* (re.inter re.allchar (re.comp (str.to_re "a")))))))) (re.++ (re.* (re.inter re.allchar (re.comp (str.to_re "a")))) ((_ re.loop 2 2) (re.++ (str.to_re "a") (re.* (re.inter re.allchar (re.comp (str.to_re "a"))))))))))))

(check-sat)
(exit)
