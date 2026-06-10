;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl style
;; [0-9] ⊆ [a-zA-Z0-9]
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
      (re.inter (re.inter (re.range "0" "9") (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9"))) (re.comp (re.range "0" "9")))
      (re.inter (re.comp (re.inter (re.range "0" "9") (re.union (re.union (re.range "a" "z") (re.range "A" "Z")) (re.range "0" "9")))) (re.range "0" "9")))))

(check-sat)
(exit)
