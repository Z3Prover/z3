; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : simple-replace-2d.smt2
(set-logic QF_S)

(declare-const a String)
(declare-const b String)
(declare-fun x_7 () String)
(declare-fun x_10 () String)

(assert (= x_10 (str.++ a b)))
(assert (= x_7 (str.replace x_10 "e" "a")))

(check-sat)

