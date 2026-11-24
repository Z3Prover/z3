; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : subsumption.smt2


(declare-const w String)

(assert (str.in_re w (re.* (str.to_re "abc"))))
(assert (str.in_re w (re.+ (str.to_re "abc"))))

(check-sat)
