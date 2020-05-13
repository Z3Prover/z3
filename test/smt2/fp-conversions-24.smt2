
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X ()  (_ FloatingPoint 11 53))

(declare-fun C () (Float64))
; - 1 = -1p0
(assert (= C ((_ to_fp 11 53) RTZ #xFFFF))) 
(assert (= C (fp #b1 #b01111111111 #x0000000000000)))

(check-sat)
(check-sat-using smt)
(exit)
