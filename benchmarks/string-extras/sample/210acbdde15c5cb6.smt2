; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/issue6005-no-strings-exp.smt2
; EXPECT: sat
; EXIT: 0
(set-logic ALL)
(declare-fun x () (Seq Int))
(assert (not (= x (seq.extract x 4 7))))
(check-sat)
