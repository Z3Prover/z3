; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/loop008.smt2
(set-logic QF_SLIA)

(set-info :status sat)

(declare-fun x () String)

(assert (= (str.++ x "ab") (str.++ "ba" x)))
(assert (> (str.len x) 5))

(check-sat)
