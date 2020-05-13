
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert (not (= (_ +oo 2 3) (fp #b0 #b11 #b00)))) ; should both be +oo

(check-sat)
(check-sat-using smt)
(exit)
