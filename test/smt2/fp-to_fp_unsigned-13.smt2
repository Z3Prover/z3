
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 5 11))

(assert (= X ((_ to_fp_unsigned 5 11) RTN #x80000000))) ; +2147483648 --> +1.9990234375p15 (last normal neg number for 5/11)
(assert (not (= X ((_ to_fp 5 11) RTZ 1.9990234375 15))))

(check-sat)
(check-sat-using smt)
(exit)
