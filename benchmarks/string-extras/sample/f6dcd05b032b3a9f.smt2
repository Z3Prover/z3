; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/issue6643-ctn-decompose-conflict.smt2
; COMMAND-LINE:
(set-logic QF_SLIA)
(declare-fun y () String)
(declare-fun z () String)
(assert (not (= (str.contains y (str.replace "A" "" z)) (str.contains y "A"))))
(set-info :status sat)
(check-sat)
