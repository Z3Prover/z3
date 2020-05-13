; Copyright (c) 2017 Microsoft Corporation
; issue #703
(set-option :smt.string_solver z3str3)
(declare-fun c0 () String)
(declare-fun c1 () String)
(define-fun e2 () String (str.replace "" c0 c1))
(assert (not (= "" e2)))
(check-sat)

(reset)
(set-option :smt.string_solver seq)
(declare-fun c0 () String)
(declare-fun c1 () String)
(define-fun e2 () String (str.replace "" c0 c1))
(assert (not (= "" e2)))
(check-sat)
