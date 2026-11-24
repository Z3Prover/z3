; origin: handwritten/generated (C. Eisenhofer) : xxabyEybaxx.smt2
(set-logic QF_S)
; e.g., x = "b", y = "b"
; or x = "", y = "a"
(set-info :status sat)

; xxaby = ybaxx
(declare-const x String)
(declare-const y String)

(assert (= (str.++ x x "ab" y) (str.++ y "ba" x x)))
(check-sat)
