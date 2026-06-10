;; Category : boolean_and_loops
;; Source   : Stanford et al. PLDI'21 / CADE 29 b-hand-made
;; Det blowup: (a|b)*a(a|b){10} via complement (DFA 2^11 states)
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "boolean_and_loops")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") ((_ re.loop 10 10) (re.union (str.to_re "a") (str.to_re "b")))) (re.comp (re.inter (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.comp (re.union ((_ re.loop 0 10) (re.union (str.to_re "a") (str.to_re "b"))) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "b") ((_ re.loop 10 10) (re.union (str.to_re "a") (str.to_re "b")))))))))
      (re.inter (re.comp (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "a") ((_ re.loop 10 10) (re.union (str.to_re "a") (str.to_re "b"))))) (re.inter (re.* (re.union (str.to_re "a") (str.to_re "b"))) (re.comp (re.union ((_ re.loop 0 10) (re.union (str.to_re "a") (str.to_re "b"))) (re.++ (re.* (re.union (str.to_re "a") (str.to_re "b"))) (str.to_re "b") ((_ re.loop 10 10) (re.union (str.to_re "a") (str.to_re "b")))))))))))

(check-sat)
(exit)
