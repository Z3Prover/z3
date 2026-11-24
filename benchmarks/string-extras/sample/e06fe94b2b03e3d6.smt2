; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/goodAI.smt2
(set-logic QF_S)

(set-info :status sat)
(declare-const input_0_1000 String)
(assert (= (str.substr input_0_1000 0 4) "good"))
(assert (= (str.substr input_0_1000 5 1) "I"))
(assert (not (= input_0_1000 "goodAI")))
(check-sat)
