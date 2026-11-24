; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : str-leq7.smt2
(set-logic QF_SLIA)

(declare-fun x () String)
(assert (= 1 (str.len x)))
(assert (str.<= "cba" x))
(check-sat)
