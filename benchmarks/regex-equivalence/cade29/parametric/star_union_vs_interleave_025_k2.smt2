;; Category : parametric
;; Source   : Kleene algebra (star-of-union)
;; (a|b)* ≡ (a*b*)*, k=2
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.* (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "b")))))))

(check-sat)
(exit)
