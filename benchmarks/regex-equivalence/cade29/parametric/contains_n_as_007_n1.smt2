;; Category : parametric
;; Source   : CADE 29 b-param style (containment)
;; At-least-1-a's: (.*a){1}.* ≡ ¬(at-most-0-a's)
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ ((_ re.loop 1 1) (re.++ (re.* re.allchar) (str.to_re "a"))) (re.* re.allchar)) (re.comp (re.* (re.inter re.allchar (re.comp (str.to_re "a"))))))))

(check-sat)
(exit)
