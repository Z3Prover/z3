; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : str-leq8.smt2
(set-logic QF_SLIA)

(declare-fun x () String)

(assert (str.<= "cba" "cab"))
(check-sat)
