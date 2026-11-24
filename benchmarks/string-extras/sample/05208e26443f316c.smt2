; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/issue5547-small-seq-len-unit.smt2
; COMMAND-LINE: --simplification=none
; EXPECT: sat
(set-logic ALL)
(declare-fun a () (Seq Int))
(declare-fun b () (Seq Int))
(assert (= a (seq.++ b (seq.unit (+ (seq.len b) 1)))))
(check-sat)
