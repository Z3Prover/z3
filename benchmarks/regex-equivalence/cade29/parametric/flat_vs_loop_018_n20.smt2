;; Category : parametric
;; Source   : CADE 29 b-param style (exponential branching)
;; Flat concat vs loop: n=20 occurrences of 'a'
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status unsat)
(set-logic QF_S)

(assert (not (= (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") (re.* (re.union (str.to_re "a") (str.to_re "b")))) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") ((_ re.loop 19 19) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a"))) (re.* (re.union (str.to_re "a") (str.to_re "b")))))))

(check-sat)
(exit)
