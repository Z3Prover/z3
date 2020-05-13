
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert (not (= #x0000FFE0 ((_ fp.to_ubv 32) RTN (fp #b0 #b11110 #b1111111111))))) ; max pos = 65504 = #xFFE0

(check-sat)
(check-sat-using smt)
(exit)
