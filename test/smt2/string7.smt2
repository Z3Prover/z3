; Copyright (c) 2017 Microsoft Corporation
; Github issue #812
(set-option :smt.string_solver z3str3)
(declare-fun c0 () String)
(declare-fun c1 () Int)
(declare-fun c2 () Int)
(assert (not (str.contains c0 (str.substr c0 c1 (- c2 c1)))))
(assert (and (<= 0 c1) (<= c1 c2) (<= c2 (str.len c0))))
(check-sat)

(reset)
(set-option :smt.string_solver seq)
(declare-fun c0 () String)
(declare-fun c1 () Int)
(declare-fun c2 () Int)
(assert (not (str.contains c0 (str.substr c0 c1 (- c2 c1)))))
(assert (and (<= 0 c1) (<= c1 c2) (<= c2 (str.len c0))))
(check-sat)

