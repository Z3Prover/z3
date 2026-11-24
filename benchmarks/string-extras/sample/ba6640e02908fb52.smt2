; origin: handwritten/generated (C. Eisenhofer) : xuabyEybaxu.smt2
(set-logic QF_S)
(set-info :status sat)

; xxabyy = yybaxx
; becomes
; xuabyv = yvbaxu
; with u = x and v = y
; as an quadratic overapproximation
(declare-const x String)
(declare-const u String)
(declare-const y String)

(assert (= (str.++ x u "ab" y) (str.++ y "ba" x u)))
(check-sat)
