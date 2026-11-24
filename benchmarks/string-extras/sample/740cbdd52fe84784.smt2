; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/intseq.smt2
; COMMAND-LINE:
;EXPECT: unsat
(set-logic ALL)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun ControlFlow (Int Int) Int)
(declare-fun s@0 () (Seq Int))
(declare-fun s@1 () (Seq Int))
(declare-fun s@2 () (Seq Int))
(assert (not
 (=> (= (ControlFlow 0 0) 170) (let ((anon0_correct  (=> (= s@0 (seq.++ (as seq.empty (Seq Int)) (seq.unit 0))) (=> (and (= s@1 (seq.++ s@0 (seq.unit 1))) (= s@2 (seq.++ s@1 (seq.unit 2)))) (and (=> (= (ControlFlow 0 135) (- 0 217)) (= (seq.len s@2) 3)) (=> (= (seq.len s@2) 3) (=> (= (ControlFlow 0 135) (- 0 224)) (= (seq.extract s@2 1 2) (seq.++ (seq.unit 1) (seq.unit 2))))))))))
(let ((PreconditionGeneratedEntry_correct  (=> (= (ControlFlow 0 170) 135) anon0_correct)))
PreconditionGeneratedEntry_correct)))
))
(check-sat)
