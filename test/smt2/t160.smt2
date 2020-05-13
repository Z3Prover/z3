
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-logic QF_NRA)
(declare-const a Real)
(assert (= (* a a) 3))
(check-sat)
