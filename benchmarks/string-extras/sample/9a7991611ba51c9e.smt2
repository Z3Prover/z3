; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/proj-issue665-nested-const.smt2
; EXPECT: sat
(set-logic ALL)
(declare-const _x (Seq Bool))
(declare-const x3 (Seq Bool))
(declare-const x (Seq Bool))
(assert (not (seq.contains x x3)))
(declare-const x1 (Seq (Seq (Seq Bool))))
(assert (seq.contains x (seq.replace _x x x3)))
(assert (seq.suffixof x1 (seq.unit (seq.unit (seq.unit false)))))
(check-sat)
