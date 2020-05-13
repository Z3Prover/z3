; Copyright (c) 2017 Microsoft Corporation
; issue #875
(set-option :smt.string_solver z3str3)

(declare-fun c0 () String)
(declare-fun c1 () String)
(declare-fun c2 () Int)
(assert (<= 0 (str.indexof c0 c1 c2)))
(assert (not (str.contains c0 c1)))
(assert (< c2 (str.len c0)))
(check-sat)

(reset)

(set-option :smt.string_solver seq)
(declare-fun c0 () String)
(declare-fun c1 () String)
(declare-fun c2 () Int)
(assert (<= 0 (str.indexof c0 c1 c2)))
(assert (not (str.contains c0 c1)))
(assert (< c2 (str.len c0)))
(check-sat)
