
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(assert (= x (fp #b0 #b11000010001 #b0000000100000011011001110100001001010000000111011110)))
(declare-fun y () FPN)
(assert (= y (fp #b1 #b11100100010 #b1001110101010110111001001110000110111010100100110111)))
(declare-fun r () FPN)
(assert (= r (_ -oo 11 53)))
(declare-fun q () FPN)
(assert (= q  (fp.mul roundTowardNegative x y)))
(assert (not (= q r)))

(check-sat)
