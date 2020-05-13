
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert (not (= #x000000FF ((_ fp.to_ubv 32) RTP (fp #b0 #b10110 #b1111110100))))) ; 254.50 RTN = 255 = #xFF (RTP)

(check-sat)
(check-sat-using smt)
(exit)
