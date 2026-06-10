;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl style
;; R ∪ R·R ⊆ R*: digit
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "inclusion_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter (re.union (re.range "0" "9") (re.++ (re.range "0" "9") (re.range "0" "9"))) (re.* (re.range "0" "9"))) (re.union (re.range "0" "9") (re.++ (re.range "0" "9") (re.range "0" "9"))))))

(check-sat)
(exit)
