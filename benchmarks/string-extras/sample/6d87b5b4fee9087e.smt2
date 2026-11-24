; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/3911.smt2
(assert (str.in.re "" ((_ re.loop 189 0) (str.to.re ""))))
(check-sat)