
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 5 11))

; variation on to_fp-4.smt2
(assert (= X ((_ to_fp 5 11) RTN #x7FFF))) ; +32767 --> +1.9990234375p14
(assert (not (= X ((_ to_fp 5 11) RTZ 32767.0 0))))

(check-sat)
(check-sat-using smt)
(exit)
