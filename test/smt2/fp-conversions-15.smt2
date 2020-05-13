
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X ()  (_ FloatingPoint 11 53))

; + 1 = +1p0
(assert (= X ((_ to_fp 11 53) RTZ #x0000000000000001)))
(assert (= X (fp #b0 #b01111111111 #x0000000000000)))

(check-sat)
(check-sat-using smt)
(exit)
