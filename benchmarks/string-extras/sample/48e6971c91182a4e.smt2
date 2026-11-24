; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/nth-model-semi-eval.smt2
; COMMAND-LINE: --produce-models
; EXPECT: sat
; EXPECT: (((seq.nth (seq.unit (- x 1)) z) 4))
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (> y 100))
(assert (= (seq.nth (seq.unit y) 10) 4))
(assert (<= y x (+ y 1)))
(assert (not (= x y)))
(assert (< 9 z 11))
(check-sat)

