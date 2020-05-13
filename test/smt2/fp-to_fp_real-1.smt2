
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-const X (_ FloatingPoint 8 24))
(declare-const R Real)

(assert (= R 1.5))
(assert (= X ((_ to_fp 8 24) RTZ R)))
(assert (not (= X ((_ to_fp 8 24) RTZ 1.5))))

(check-sat)
(check-sat-using smt)
(exit)
