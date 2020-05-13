
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 5 11))

(assert (= X ((_ to_fp 5 11) RTN #x7FFF))) ; +32767 --> +1.9990234375p14
(assert (not (= X ((_ to_fp 5 11) RTZ 1.9990234375 14))))

(check-sat)
(check-sat-using smt)
(exit)
