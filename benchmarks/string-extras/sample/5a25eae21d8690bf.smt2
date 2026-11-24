; origin: handwritten/generated (C. Eisenhofer) : abczExvAbcxEywAcyEzx.smt2
(set-logic QF_S)
(set-info :status unknown)

; abcz = xv & bcx = yw & cy = zx
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const v String)
(declare-const w String)

(assert (= (str.++ "abc" z) (str.++ x v)))
(assert (= (str.++ "bc" x) (str.++ y w)))
(assert (= (str.++ "c" y) (str.++ z x)))
(check-sat)
