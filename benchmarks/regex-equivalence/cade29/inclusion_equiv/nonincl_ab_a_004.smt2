;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl style
;; (a|b)* ⊄ a*
;; Status   : sat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "inclusion_equiv")
(set-info :status sat)
(set-logic QF_S)

(assert (not (= (re.inter (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.* (str.to_re "a"))) (re.* (re.union (str.to_re "a") (str.to_re "b"))))))

(check-sat)
(exit)
