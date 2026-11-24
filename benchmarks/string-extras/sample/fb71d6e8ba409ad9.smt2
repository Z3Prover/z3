; origin: handwritten/generated (C. Eisenhofer) : azExyAbxEyzAcyEzx.smt2
(set-logic QF_S)
(set-info :status unknown)

; az = xy & bx = yz & cy = zx
(declare-const x String)
(declare-const y String)
(declare-const z String)

(assert (= (str.++ "a" z) (str.++ x y)))
(assert (= (str.++ "b" x) (str.++ y z)))
(assert (= (str.++ "c" y) (str.++ z x)))
(check-sat)
