
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

; should be ok as long as the arith or fpa simplifier eliminates fp.to_real.
(assert (= (- 3.0) (fp.to_real (fp #b1 #b10000000000 #x8000000000000))))

(check-sat)
(check-sat-using smt)
(exit)
