; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : norn-benchmark-9h.smt2
(set-logic QF_S)

(declare-fun var_0 () String)
(declare-fun var_1 () String)
(declare-fun var_2 () String)
(declare-fun var_3 () String)
(declare-fun var_4 () String)
(declare-fun var_5 () String)
(declare-fun var_6 () String)
(declare-fun var_7 () String)
(declare-fun var_8 () String)

(assert (str.in_re var_0 (str.to_re "abc")))
(assert (str.in_re var_1 (str.to_re "abc")))
(assert (not (= var_0 var_1)))
(check-sat)
