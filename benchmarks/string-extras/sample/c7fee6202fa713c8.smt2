; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : periodic-neg-eq-ab-star.smt2
(set-logic QF_SLIA)
(set-info :status unsat)

(declare-fun x () String)
(declare-fun y () String)

(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (not (= (str.++ x y) (str.++ y x))))

(check-sat)
