; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/issue6072-inc-no-const-reg.smt2
; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun i4 () Int)
(declare-fun str5 () String)
(assert (= (str.++ str5 (str.from_int i4)) (str.++ "15" str5 "1")))
(push)
(check-sat)
(pop)
(check-sat)
