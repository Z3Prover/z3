; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/stoi-solve.smt2
(set-logic ALL)
(set-info :status sat)

(declare-fun x () String)
(assert (= (str.to_int x) 12345)) 
(check-sat)
