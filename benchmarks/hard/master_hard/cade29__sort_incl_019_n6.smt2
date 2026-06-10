;; Category : inclusion_equiv
;; Source   : CADE 29 b-armc-incl (sorting style)
;; Adjacent swaps ⊆ all digit pairs, n=6
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "inclusion_equiv")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.inter ((_ re.loop 6 6) (re.union (re.++ (str.to_re "0") (str.to_re "1")) (re.++ (str.to_re "1") (str.to_re "2")) (re.++ (str.to_re "2") (str.to_re "3")) (re.++ (str.to_re "3") (str.to_re "4")) (re.++ (str.to_re "4") (str.to_re "5")))) ((_ re.loop 6 6) (re.++ (re.range "0" "9") (re.range "0" "9")))) ((_ re.loop 6 6) (re.union (re.++ (str.to_re "0") (str.to_re "1")) (re.++ (str.to_re "1") (str.to_re "2")) (re.++ (str.to_re "2") (str.to_re "3")) (re.++ (str.to_re "3") (str.to_re "4")) (re.++ (str.to_re "4") (str.to_re "5")))))))

(check-sat)
(exit)
