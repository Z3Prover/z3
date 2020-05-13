
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 5 11))

(assert (= X ((_ to_fp 5 11) RTZ #x000000000000000000001)))  ; +1.0
(assert (not (= X ((_ to_fp 5 11) RTZ 1.0 0))))

(check-sat)
(check-sat-using smt)
(exit)
