; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/4041.smt2
(declare-fun a () String)
(declare-fun b () String)
(assert (distinct (str.substr (str.++ a "ab" b) 0 (+ (str.len a) 1)) (str.++ a "a")))
(check-sat)