
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ BitVec 8))
(assert (= X ((_ fp.to_sbv 8) RTZ (fp #b1 #b00000 #b0000000000)))) ; -0.0
(assert (not (= X #x00)))

(check-sat)
(check-sat-using smt)
(exit)
