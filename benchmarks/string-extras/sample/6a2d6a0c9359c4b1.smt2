; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/issue5543-unit-cmv.smt2
; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(declare-fun a () (Seq (Seq Int)))
(declare-fun b () (Seq (Seq Int)))
(declare-fun c () (Seq (Seq Int)))
(declare-fun d () (Seq (Seq Int)))
(declare-fun e () (Seq Int))
(declare-fun f () (Seq Int))
(assert (distinct a (seq.++ (seq.unit e) b)))
(assert (= (seq.++ (seq.unit f) d) a c))
(check-sat)
