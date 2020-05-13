; Copyright (c) 2018 Microsoft Corporation
; GitHub issue

(set-logic QF_FP)
(declare-fun fp_a ()(_ FloatingPoint 8 24))
(declare-fun fp_b ()(_ FloatingPoint 8 24))
(assert (fp.lt fp_b fp_a))
(assert (fp.eq fp_b fp_a))
(assert (not (fp.eq (fp.add RTZ fp_a fp_a) fp_b)))
(assert (not (fp.isNaN (fp.mul RTP fp_a fp_a))))
(assert (not (fp.isZero (fp.mul RTN fp_a fp_a))))
(assert (not (fp.isNaN (fp.sub RTZ fp_a (fp #b1 #b10000100 #b01101000010000100000110)))))
(assert (fp.gt (fp.mul RNE (fp #b1 #b10001110 #b00110010000001100101100) (_ -oo 8 24)) (fp.div RTP fp_b fp_b)))
(assert (not (fp.eq (fp.div RTP (fp #b1 #b10001100 #b00000001000010100100101) (fp #b1 #b00000000 #b11100011100110101010111)) (fp.mul RTN (fp #b0 #b10000100 #b10000011111101011100000) (_ NaN 8 24)))))
(assert (not (fp.isNaN (fp.add RTP fp_a fp_b))))
(check-sat)