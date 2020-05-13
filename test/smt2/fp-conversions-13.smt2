
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X ()  (_ FloatingPoint 11 53))

; small floats, 1 = +1p0
(declare-fun T () (_ FloatingPoint 3 3))
(assert (= T ((_ to_fp 3 3) RTZ #b00001))) 
(assert (= T (fp #b0 #b011 #b00)))

(check-sat)
(check-sat-using smt)
(exit)
