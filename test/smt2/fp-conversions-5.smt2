
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert (not (= (_ +zero 2 4) (fp #b0 #b00 #b000)))) ; should both be +0

(check-sat)
(check-sat-using smt)
(exit)
