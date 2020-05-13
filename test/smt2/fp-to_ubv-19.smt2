
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert (not (= #xFE ((_ fp.to_ubv 8) RNE (fp #b0 #b10110 #b1111110100))))) ; 254.50 RNE = 254 = xFE

(check-sat)
(check-sat-using smt)
(exit)
