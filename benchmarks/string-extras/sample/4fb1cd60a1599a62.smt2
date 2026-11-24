; origin: handwritten/generated (C. Eisenhofer) : xabyEyabxAxabyEbyax.smt2
(set-logic QF_S)
(set-info :status unsat)

; xaby = yabx & xaby = byax
(declare-const x String)
(declare-const y String)

(declare-const z String) ; just to avoid the EUF solver to equate them in the advantageous way
(declare-const w String)

(assert (= (str.++ x "ab" y z) (str.++ y "ab" x w)))
(assert (= (str.++ x "ab" y) (str.++ "b" y "a" x)))
(check-sat)
