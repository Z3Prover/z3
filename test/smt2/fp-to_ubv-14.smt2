
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

; 254.875 RTP = 255 = XFF
(assert (not (= #xFF ((_ fp.to_ubv 8) RTP (fp #b0 #b10110 #b1111110111))))) 

(check-sat)
(check-sat-using smt)
(exit)
