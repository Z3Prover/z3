; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/issue8906-oob-exp.smt2
; COMMAND-LINE: --produce-models
; EXPECT: sat
(set-logic ALL)
(declare-const x1 Bool)
(declare-const x Int)
(assert (forall ((e String)) (or (exists ((e String)) (or (ite (str.prefixof "-" (str.at e 0)) false (= 1 (str.to_int (str.at e (+ x (str.len e)))))) x1)))))
(check-sat)
