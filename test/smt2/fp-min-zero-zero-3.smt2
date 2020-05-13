; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FP)
(set-info :status sat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)

(assert (= x (fp.min (_ +zero 11 53) (_ -zero 11 53))))
(assert (= y (fp.min (_ -zero 11 53) (_ +zero 11 53))))
(assert (not (= x y)))

(check-sat)
(get-value (x))
(get-value (y))
(check-sat-using smt)
(get-value (x))
(get-value (y))
(exit)
