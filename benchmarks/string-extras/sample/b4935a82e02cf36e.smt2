; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/seq/issue8148-2-const-mv.smt2
; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(assert (forall ((V Int)) (= 0 (seq.nth (seq.unit 0) 1))))
(check-sat)
