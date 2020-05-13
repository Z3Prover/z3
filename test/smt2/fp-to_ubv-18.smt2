
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ BitVec 8))

(assert (= X ((_ fp.to_ubv 8) RNA (fp #b0 #b10110 #b1111110100)))) ; 254.50 RNA = 255 = xFF
(assert (not (= X #xFF )))

(check-sat)
(check-sat-using smt)
(exit)
