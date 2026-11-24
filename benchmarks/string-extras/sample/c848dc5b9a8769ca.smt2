; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : negated-equation-1.smt2
(declare-fun a () String)
(assert (not (= (str.at a 0) (str.at "" 0))))
(assert (= (str.len a) 0))
(check-sat)
