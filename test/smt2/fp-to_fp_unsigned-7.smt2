
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 5 11))

(assert (= X ((_ to_fp_unsigned 5 11) RTN #xFFFF))) ; +65535 --> +1.9990234375p15 (max pos)
(assert (not (= X ((_ to_fp 5 11) RTN 65535.0 0))))

(check-sat)
(check-sat-using smt)
(exit)
