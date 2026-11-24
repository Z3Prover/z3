; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/dd_a68_pp_static.smt2
; EXPECT: unsat
(set-logic ALL)
(declare-fun u () String)
(assert (not (= 0 (ite (= "pr" (str.replace (str.substr u 0 1) "A" "")) 1 0))))
(check-sat)
