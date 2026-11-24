; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : hu-benchmarks/concat_sat.smt2
; sat
(declare-fun x ()String)
(declare-fun y ()String)
(declare-fun z ()String)

(declare-const len_x Int)
(declare-const len_y Int)
(declare-const len_z Int)

(assert (= len_x (str.len x)))
(assert (= len_y (str.len y)))
(assert (= len_z (str.len z)))

(assert (< 1 len_x))
(assert (< 3 len_y))
(assert (> 7 len_z))

(assert (= z (str.++ x y)))

(check-sat)
