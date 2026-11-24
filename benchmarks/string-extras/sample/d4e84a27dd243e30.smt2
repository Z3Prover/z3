; origin: handwritten/generated (C. Eisenhofer) : diseq.smt2
(set-logic QF_S)

(declare-const X String)
(declare-const Y String)

(assert (distinct X "" (str.++ X "a") "b" "a" Y))
(assert (= (str.++ X "a") (str.++ "a" Y)))

(check-sat)
