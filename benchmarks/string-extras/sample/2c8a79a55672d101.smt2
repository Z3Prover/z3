; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : hu-benchmarks/indexof_const_startpos_unsat.smt2
(set-info :status unsat)
(declare-fun a () String)
(declare-fun b () String)

(declare-fun i () Int)
(declare-fun j () Int)


(assert (= "hhhhjjj" (str.++ "h" a)))
(assert (= (str.indexof a "hhh" j) i))
(assert (>= i 0))
(assert (= j 1))
(check-sat)
