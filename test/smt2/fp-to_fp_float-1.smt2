
; Copyright (c) 2015 Microsoft Corporation
; 
; This script shows what possibly is a bug in the cast operation from a smaller to a bigger format.
; Subnormal numbers in the IEEE single precision format (8,24) are those with exponent -127.
; Thus subnormal numbers have values 0.m * 2^-126.
; Thus in absolute value 2^-126 is the smallest representable normal in (8,24). 
; One would expect that large = cast(small) and large = 1* 2^-127.

(set-logic QF_FP)
(set-info :status unsat)
(set-option :produce-models true)

(declare-fun large () ( _ FloatingPoint 11 53 ))
(declare-fun cast () ( _ FloatingPoint 11 53 ))
(declare-fun small () ( _ FloatingPoint 8 24 ))

(assert (= small ((_ to_fp 8 24) roundNearestTiesToEven 0.5 (- 126))))
(assert (= large ((_ to_fp 11 53 ) roundNearestTiesToEven 0.5 (- 126))))

(assert (= cast ((_ to_fp 11 53)  roundNearestTiesToEven small)))
(assert (not (= cast ((_ to_fp 11 53) roundNearestTiesToEven 1.0 (- 127)))))

(check-sat)
(check-sat-using smt)
