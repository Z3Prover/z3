; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : str.at-3b.smt2
(set-logic QF_S)

(declare-const x String)

(assert (= (str.at x (- (str.len x) 1)) "x"))
(assert (= (str.at x (- (str.len x) 2)) "y"))
(assert (< (str.len x) 2))

(check-sat)
