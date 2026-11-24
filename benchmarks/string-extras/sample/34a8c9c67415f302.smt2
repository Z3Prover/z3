; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : chars3.smt2
(set-logic ALL)

(declare-fun Constructed_Argument () String)

(assert (let ((a!1 (to_real (str.indexof Constructed_Argument
                                 (str.++ (str.from_code (bv2nat #x2d)) (str.from_code (bv2nat #x2d)))
                                 0))))
  (= a!1 (- 1.0))))

(check-sat)
