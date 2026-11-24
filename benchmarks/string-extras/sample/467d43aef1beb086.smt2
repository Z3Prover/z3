; origin: handwritten/generated (C. Eisenhofer) : xuabyvEyvbaxu.smt2
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
(declare-const v String)

(assert (= (str.++ x u "ab" y v) (str.++ y v "ba" x u)))
(check-sat)
