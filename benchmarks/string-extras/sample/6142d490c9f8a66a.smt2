; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/4044.smt2
(declare-fun s () String)
(assert (distinct (str.suffixof "B" (str.++ s "B")) (= s "")))
(check-sat)