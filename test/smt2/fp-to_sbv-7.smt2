;; Copyright (c) 2015 Microsoft Corporation

(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")
(set-option :model.completion true)

; 2^15 = 32768 -> unspecified
(assert (not (= #x00 ((_ fp.to_sbv 8) RTP (fp #b0 #b11110 #b0000000000)))))

(check-sat)
(check-sat-using smt)
(exit)
