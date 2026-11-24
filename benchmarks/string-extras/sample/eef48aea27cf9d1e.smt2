; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/4019.smt2
(declare-fun a () String)
(assert (= "" (str.replace "" a "B")))
(check-sat)