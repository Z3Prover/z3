
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert (not (= (_ NaN 6 8) (fp #b0 #b111111 #b0000001)))) ; should both be NaNs

(check-sat)
(check-sat-using smt)
(exit)
