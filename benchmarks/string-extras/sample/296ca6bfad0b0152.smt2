; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/str007.smt2
(set-logic QF_S)
(set-info :status unsat)

(declare-fun x () String)
(declare-fun y () String)


(assert (or (= x y) (= x y)))

(assert (= (str.++ x "ba") (str.++ "ab" x)))
(assert (= (str.++ y "ab") (str.++ "ab" y)))

(check-sat)
