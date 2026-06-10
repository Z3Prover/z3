;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl style
;; [a-z] ⊆ [a-zA-Z]
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
      (re.inter (re.inter (re.range "a" "z") (re.union (re.range "a" "z") (re.range "A" "Z"))) (re.comp (re.range "a" "z")))
      (re.inter (re.comp (re.inter (re.range "a" "z") (re.union (re.range "a" "z") (re.range "A" "Z")))) (re.range "a" "z")))))

(check-sat)
(exit)
