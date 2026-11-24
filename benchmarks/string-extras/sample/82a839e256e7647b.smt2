; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : regex_range.smt2
(set-logic QF_SLIA)

(declare-const w String)

(assert (str.in_re w (re.range "ab" "c")))

(check-sat)
