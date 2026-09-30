; Regression for Z3Prover/z3#10954: the clause log prints the Real constants as
; (/ 1.0 3.0) and (/ 1.0 4.0). The replay used to keep them as division terms, so
; the arithmetic checker could not close the farkas sum and fell back to the SMT
; solver. Expected matrix class for smt-clause-log and smt-clause-log-nopp:
; verified, with no farkas miss.
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= (- x y) (/ 1.0 3.0)))
(assert (<= (- x y) (/ 1.0 4.0)))
(check-sat)
