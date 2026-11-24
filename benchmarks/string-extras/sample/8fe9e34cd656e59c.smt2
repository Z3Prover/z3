; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : substring.smt2
(set-logic QF_S)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun n () Int)

(assert (= y (str.substr x n 5)))
(assert (>= (str.len x) (+ n 5)))
(assert (= (str.at y 0) "a"))
(assert (> n 0))

(check-sat)
