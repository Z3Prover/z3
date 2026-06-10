;; Category : parametric
;; Source   : Kleene algebra (star-of-union)
;; (a|b|c|d|e)* ≡ (a*b*c*d*e*)*, k=5
;; Status   : unsat
;;
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "parametric")
(set-info :status unsat)
(set-logic QF_S)

(assert
  (not
    (=
      (re.inter (re.* (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "d") (str.to_re "e"))) (re.comp (re.* (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "b")) (re.* (str.to_re "c")) (re.* (str.to_re "d")) (re.* (str.to_re "e"))))))
      (re.inter (re.comp (re.* (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c") (str.to_re "d") (str.to_re "e")))) (re.* (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "b")) (re.* (str.to_re "c")) (re.* (str.to_re "d")) (re.* (str.to_re "e"))))))))

(check-sat)
(exit)
