; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/nth-concat-unit.smt2
; EXPECT: unsat
; SEQ_NTH_EVAL_SYM must have a complete proof with an empty prefix.
(set-logic ALL)
(declare-const x String)
(declare-const s (Seq String))
(assert (distinct (seq.nth (seq.++ (seq.unit x) s) 0) x))
(check-sat)
