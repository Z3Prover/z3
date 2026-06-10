;; Category : parametric
;; Source   : CADE 29 b-param (long strings)
;; (ABC){n}·ABC ≡ ABC·(ABC){n}, n=5
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ ((_ re.loop 5 5) (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c"))) (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c"))) (re.++ (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c")) ((_ re.loop 5 5) (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c")))))))

(check-sat)
(exit)
