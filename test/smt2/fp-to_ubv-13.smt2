
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

; 254.875 RTN = 254 = xFE
(assert (not (= #xFE ((_ fp.to_ubv 8) RTN (fp #b0 #b10110 #b1111110111))))) 

(check-sat)
(check-sat-using smt)
(exit)
