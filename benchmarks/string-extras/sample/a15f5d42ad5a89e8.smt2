; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/seq-eval-extract.smt2
; EXPECT: unsat
(set-logic ALL)
(assert
(not
(=
(seq.extract
(seq.++ (seq.unit 1) (seq.unit 2))
0 -1)
(as seq.empty (Seq Int)))))
(check-sat)
