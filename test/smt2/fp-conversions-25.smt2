
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X ()  (_ FloatingPoint 11 53))

(declare-fun C () (Float64))
; + 2 = +1p1
(assert (= C ((_ to_fp 11 53) RTZ #x0000000000000002)))
(assert (= C (fp #b0 #b10000000000 #x0000000000000)))

(check-sat)
(check-sat-using smt)
(exit)
