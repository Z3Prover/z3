; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : str-leq14.smt2
(set-logic QF_SLIA)

(declare-fun x () String)
(assert (str.in_re x (str.to_re "a")))
(assert (str.<= "abc" x))
(check-sat)
