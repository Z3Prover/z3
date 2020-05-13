
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun y () Real)

(assert (= y (fp.to_real (fp #b0 #b10000000100 #x5000000000000))))

(check-sat)
(get-value (y))
(check-sat-using smt)
(get-value (y))
(exit)
