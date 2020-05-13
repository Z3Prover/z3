; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)

(assert (= x (fp.min (_ -zero 11 53) (_ +zero 11 53))))

(assert (not (or (= x (_ -zero 11 53))
				 (= x (_ +zero 11 53)))))

(check-sat)
(check-sat-using smt)
(exit)
