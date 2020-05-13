
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X ()  (_ FloatingPoint 11 53))

 ; -9223372036854775808 = 2^63 = -1p63
(assert (= X ((_ to_fp 11 53) RTZ #x8000000000000000)))
(assert (= X (fp #b1 #b10000111110 #x0000000000000)))

(check-sat)
(check-sat-using smt)
(exit)
