; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : monadic-length.smt2

(declare-const x String)
(declare-const a Int)
(declare-const b Int)

(assert (= (str.len x) a))
(assert (> a 5))
(assert (< a 10))
(assert (str.in_re x (re.* (str.to_re "abc"))))

(check-sat)
