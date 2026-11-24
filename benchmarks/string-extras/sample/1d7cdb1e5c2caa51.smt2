; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : str-leq-reflexive.smt2
(set-logic QF_SLIA)

(assert (str.<= "a" "b"))
(assert (str.<= "a" "a"))
(check-sat)
