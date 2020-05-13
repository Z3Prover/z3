
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X ()  (_ FloatingPoint 11 53))

; downcast Float64 -> Float32
(declare-fun S () (Float32))
(assert (= S ((_ to_fp 8 24) roundTowardZero S)))
(assert (= X ((_ to_fp 11 53) #x0000000000000000)))
(assert (not (= X (fp #b0 #b00000000000 #x0000000000000))))

(check-sat)
(check-sat-using smt)
(exit)
