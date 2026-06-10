;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl style
;; A* ⊆ (A|B)*: a_ab
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "inclusion_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.inter (re.* (str.to_re "a")) (re.* (re.union (str.to_re "a") (str.to_re "b")))) (re.comp (re.* (str.to_re "a"))))
      (re.inter (re.comp (re.inter (re.* (str.to_re "a")) (re.* (re.union (str.to_re "a") (str.to_re "b"))))) (re.* (str.to_re "a"))))))

(check-sat)
(exit)
