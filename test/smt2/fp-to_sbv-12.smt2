
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-const X (_ BitVec 8))
; -1.9921875p6 == -127.5 -> -128 = #x80 because of RTP
(assert (= X ((_ fp.to_sbv 8) RTP (fp #b1 #b10101 #b1111111000))))
(assert (not (= X #x81)))

(check-sat)
(check-sat-using smt)
(exit)
