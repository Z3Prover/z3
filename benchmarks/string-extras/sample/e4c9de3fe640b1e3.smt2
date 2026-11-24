; origin: handwritten/generated (C. Eisenhofer) : xabyEybaxALxG1000.smt2
(set-logic QF_S)
(set-info :status sat)

; xaby = ybax && |x| > 1000
(declare-const x String)
(declare-const y String)

(assert (= (str.++ x "ab" y ) (str.++ y "ba" x)))
(assert (> (str.len x) 1000))
(check-sat)
