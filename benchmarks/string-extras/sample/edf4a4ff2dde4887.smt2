; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/seq-ex5-dd.smt2
; COMMAND-LINE:
(set-logic ALL)
(set-info :status sat)
(declare-fun z () (Seq Int))
(declare-fun i () Int)
(declare-fun n () Int)
(assert (> i 777))
(assert (= (seq.extract z n 1) (seq.unit i)))
(check-sat)
