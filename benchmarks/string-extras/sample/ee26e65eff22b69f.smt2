; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/proj-issue753-ae.smt2
; EXPECT: unsat
(set-logic ALL)
(check-sat-assuming ((seq.prefixof (seq.++ (seq.unit false) (seq.unit false)) (seq.unit false))))
