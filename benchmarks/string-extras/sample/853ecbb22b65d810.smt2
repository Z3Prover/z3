; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/seq-nth.smt2
; COMMAND-LINE:
;EXPECT: sat
(set-logic ALL)
(declare-fun s () (Seq Int))
(assert (= 5 (seq.nth s 5)))
(assert (= 2 (seq.len s)))
(check-sat)
