; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/seq-ex4.smt2
; COMMAND-LINE:
(set-logic ALL)
(set-info :status unsat)
(declare-fun z () (Seq Int))
(declare-fun i () Int)
(declare-fun n () Int)
(assert (= (seq.extract z n 1) (seq.unit i)))
(assert (< (seq.len z) n))
(check-sat)
