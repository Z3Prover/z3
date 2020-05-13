
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 5 11))

(assert (= X ((_ to_fp_unsigned 5 11) RTP #x8001))) ; +32769 = +1.0009765625p15
(assert (not (= X ((_ to_fp 5 11) RTP 32769.0 0))))

(check-sat)
(check-sat-using smt)
(exit)
