; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/leq.smt2
; COMMAND-LINE:
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (or
  (not (str.<= (str.++ "A" x) (str.++ "B" y)))
  (not (str.<= (str.++ "A" x) (str.++ "BC" y)))
  (str.<= (str.++ "A" "D" x) (str.++ "AC" y))))
(set-info :status unsat)
(check-sat)
