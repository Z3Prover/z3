; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : suffix-2.smt2
(set-logic QF_S)

(declare-const x String)

(assert (not (= (str.suffixof x "A") true)))

(check-sat)
