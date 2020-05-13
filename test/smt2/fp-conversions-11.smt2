
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X ()  (_ FloatingPoint 11 53))

; upcast Float32 -> Float64
(declare-fun S () (Float32))
(assert (= S ((_ to_fp 8 24) #xC0000000)))
(assert (= X ((_ to_fp 11 53) roundTowardZero S)))
(assert (not (= X (fp #b1 #b10000000000 #x0000000000000))))

(check-sat)
(check-sat-using smt) 
(exit)
