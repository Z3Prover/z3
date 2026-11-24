; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/3999.smt2
(declare-fun a () String)
(declare-fun b () Int)
(assert (= (str.replace "A" (int.to.str b) a) "A"))
(check-sat)