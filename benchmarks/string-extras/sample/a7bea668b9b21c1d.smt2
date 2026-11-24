; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/3700.smt2
(set-option :model_validate true)
(set-option :smt.arith.random_initial_value true)
(set-option :rewriter.eq2ineq true)
(declare-fun a () Int)
(assert (distinct (str.indexof "" "" a) 0))
(check-sat)