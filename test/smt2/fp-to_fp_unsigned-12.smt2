
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 5 11))

(assert (= X ((_ to_fp_unsigned 5 11) RTP #x80000000))) ; +2147483648 --> +oo (too large; rounding)
(assert (not (= X (_ +oo 5 11))))

(check-sat)
(check-sat-using smt)
(exit)
