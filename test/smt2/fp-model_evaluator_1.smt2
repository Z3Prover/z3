
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status sat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(declare-fun r () FPN)
(declare-fun q () FPN)

(assert (= x (fp #b0 #b00010110010 #b1011000000000111000000101011000111101100000100000001)))
(assert (= r (fp #b0 #b00010110010 #b1011000000000111000000101011000111101100000100000001)))
(assert (= q (fp.abs x)))

(assert (= q r))

(check-sat)
(check-sat-using smt)
(get-model)
