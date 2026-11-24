; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : simple-cvc-smtlib-b.smt2

(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun a_len () Int)

(assert (= b (str.++ a "c")))
(assert (= (str.len a) (str.len b)))
(assert (str.in_re a (re.* (str.to_re "xy"))))
(assert (not (str.in_re b (re.* (str.to_re "xy")))))
(assert (= (str.len a) a_len))
(assert (> a_len 0))

(check-sat)