; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/4015.smt2
(declare-fun a () String)
(declare-fun b () String)
(set-option :smt.random_seed 6) 
(assert (distinct (str.contains (str.replace "B" a b) b) (str.prefixof a (str.replace "" b a))))
(check-sat)