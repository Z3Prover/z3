
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert (not (= (_ -zero 3 2) (fp #b1 #b000 #b0)))) ; should both be -0

(check-sat)
(check-sat-using smt)
(exit)
