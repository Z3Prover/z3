; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : hu-benchmarks/indexof_empty_unsat.smt2
(set-info :status unsat)
(declare-fun a () String)
(declare-fun b () String)

(declare-fun i () Int)
(declare-fun j () Int)

(assert (str.in_re a (re.union (str.to_re "hhhbbb") (str.to_re "bhhh"))))
(assert (= (str.indexof a "" j) i))
(assert (not (= i j)))
(assert (>= i 0))
(check-sat)
