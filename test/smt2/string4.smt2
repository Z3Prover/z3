; Copyright (c) 2017 Microsoft Corporation
; Issuue 963
(set-option :smt.string_solver z3str3)
(declare-fun c2 () Int)
(assert (<= 0 c2))
(assert (<= c2 8))
(assert (not (<= 0 (str.indexof "a123cdef" (str.substr "a123cdef" 0 c2) 0))))
(check-sat)

(exit)

; in a regression, seq returns sat with an invalid model
(reset)
(set-option :smt.string_solver seq)
(set-option :model_validate true)
(declare-fun c2 () Int)
(assert (<= 0 c2))
(assert (<= c2 8))
(assert (not (<= 0 (str.indexof "a123cdef" (str.substr "a123cdef" 0 c2) 0))))
(check-sat)
(get-model)