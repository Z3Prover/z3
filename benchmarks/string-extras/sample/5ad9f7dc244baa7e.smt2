; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : str.from_int.smt2

(declare-const w String)

(assert (= w (str.from_int 42)))
(assert (str.in_re w (re.* (re.range "2" "4"))))
(check-sat)
