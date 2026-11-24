; origin: handwritten/generated (C. Eisenhofer) : shiftedPower.smt2
(set-logic QF_S)

(declare-fun pow (String Int) String)
(declare-const m Int)
(declare-const n Int)
(declare-const x String)
(declare-const y String)

(assert (= 
    (pow "abc" m)
    (str.++ "a" (pow "bca" n) "bc")
))

(check-sat)