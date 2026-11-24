; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/prefix-multi-var-emp.smt2
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(declare-fun u () String)
(assert (= "" (str.++ x y x w y z)))
(assert (not (= w "")))
(check-sat)
