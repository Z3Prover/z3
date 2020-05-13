
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ BitVec 8))
(assert (= X ((_ fp.to_sbv 8) RTP ((_ to_fp 5 11) RTZ -42.0)))) ; -42
(assert (not (= X #xD6)))

(check-sat)
(check-sat-using smt)
(exit)
