
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert (not (= #x00008000 ((_ fp.to_ubv 32) RTN (fp #b0 #b11110 #b0000000000))))) ; 32768 = #x8000

(check-sat)
(check-sat-using smt)
(exit)
