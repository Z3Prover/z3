
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(assert (= x (fp #b1 #b11000100001 #b0000000001010011100111010011001001100101101011100110)))
(declare-fun r () FPN)
(assert (= r (fp #b1 #b11000100001 #b0000000001010011100111010011001001100101101011100110)))
(assert (not (= (fp.roundToIntegral roundTowardZero x) r)))

(check-sat)
(check-sat-using smt)
