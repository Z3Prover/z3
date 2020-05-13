;; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

; +oo -> (_ fp.to_ubv_unspecified 8)
(assert (not (= #x00 ((_ fp.to_ubv 8) RTP (_ +oo 5 11)))))

(check-sat)
(check-sat-using smt)
(exit)
