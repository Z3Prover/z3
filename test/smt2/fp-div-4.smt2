
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(declare-fun y () FPN)
(declare-fun r () FPN)
(declare-fun q () FPN)

(assert (= x (fp #b0 #b11011000011 #b1100111010010111000011100010011101000011101101100001)))
(assert (= y (fp #b1 #b01011000011 #b1111010111110011001011001111101011010100101111000000)))
(assert (= r (fp #b1 #b11111111110 #b1101011111011010001000100110100101001001010010110111)))
(assert (= q (fp.div roundTowardZero x y)))

(assert (not (= q r)))
(check-sat)
(check-sat-using smt)
