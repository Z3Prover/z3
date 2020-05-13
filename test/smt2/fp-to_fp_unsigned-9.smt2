
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 5 11))
(declare-fun RM1 () RoundingMode)
(declare-fun RM2 () RoundingMode)

(assert (not (= RM1 RM2)))

; #xFFE0 = 65504 is the last precisely representable number in FP 5/11
(assert (not (= 
	       ((_ to_fp_unsigned 5 11) RM1 #xFFE0)
	       ((_ to_fp_unsigned 5 11) RM2 #xFFE0))))

(check-sat)
(check-sat-using smt)
(exit)
