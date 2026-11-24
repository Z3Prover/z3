; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/string9.smt2
; Copyright (c) 2017 Microsoft Corporation
; Github issue #684

(declare-const c0 String)
(define-fun e1 () Bool (= "barbar" c0))
(define-fun e2 () Bool (not e1))
(define-fun e3 () Bool (str.contains c0 "barbar"))
(assert e2)
(assert e3)
(check-sat)
(eval (= c0 "barbar"))
