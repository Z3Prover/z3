; origin: handwritten/generated (C. Eisenhofer) : xabyEybax.smt2
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)
(declare-const y String)

(assert (= (str.++ x "ab" y) (str.++ y "ba" x)))
(check-sat)
