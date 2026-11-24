; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/issue8918-str-nth-crange-red.smt2
; REQUIRES: no-safe-mode
; COMMAND-LINE: --no-strings-lazy-pp
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(assert (<= (str.to_int (str.++ "0" (str.from_int (ite (str.prefixof "-" (str.at a 2)) 0 (str.to_int (str.at a 2)))))) (- 1)))
(check-sat)
