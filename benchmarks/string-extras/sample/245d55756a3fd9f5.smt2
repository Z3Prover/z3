; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/seq-eval-contains.smt2
; EXPECT: unsat
(set-logic ALL)
(assert
(not
(seq.contains
(seq.++ (seq.unit 1) (seq.unit 2))
(seq.unit 1))))
(check-sat)
