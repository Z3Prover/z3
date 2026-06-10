;; Category : parametric
;; Source   : Kleene algebra (star-of-union)
;; (a|b|c)* ≡ (a*b*c*)*, k=3
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
      (re.inter (re.* (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c"))) (re.comp (re.* (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "b")) (re.* (str.to_re "c"))))))
      (re.inter (re.comp (re.* (re.union (str.to_re "a") (str.to_re "b") (str.to_re "c")))) (re.* (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "b")) (re.* (str.to_re "c"))))))))

(check-sat)
(exit)
