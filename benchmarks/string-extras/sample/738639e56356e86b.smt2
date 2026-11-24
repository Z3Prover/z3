; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/issue5940-2-skc-len-conc.smt2
; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.prefixof (str.replace x x (str.replace "A" x "")) (str.replace "" x "A")) (= (not (= (not (not (= (= (str.prefixof (str.replace "A" x "") x) (str.prefixof "A" x)) (str.prefixof x x)))) (str.prefixof (str.replace "A" x "") (str.replace "A" "A" "")))) (str.prefixof x "A")))))
(check-sat)
