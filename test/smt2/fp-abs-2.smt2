
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(assert (= x (fp #b0 #b00111100111 #b1000101010000000111011101011100100000111110011101000)))
(declare-fun r () FPN)
(assert (= r (fp #b0 #b00111100111 #b1000101010000000111011101011100100000111110011101000)))
(assert (not (= (fp.abs x) r)))

(check-sat)
(check-sat-using smt)
