
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(declare-const x (_ FloatingPoint 5 7))
(declare-const y (_ FloatingPoint 5 7))
(declare-const r1 (_ FloatingPoint 5 7))
(declare-const r2 (_ FloatingPoint 5 7))

(define-const nan (_ FloatingPoint 5 7) (_ NaN 5 7))

(assert (not (= nan x)))
(assert (not (= nan y)))
(assert (not (= nan r1)))
(assert (not (= nan r2)))

(assert (= r1 (fp.mul roundNearestTiesToEven x y)))
(assert (= r2 (fp.mul roundNearestTiesToEven y x)))
(assert (not (fp.eq r1 r2)))

(check-sat)
