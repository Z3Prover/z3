
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status sat)

(declare-fun sf1 () (Float16))
(declare-fun sf2 () (Float32))
(declare-fun sf3 () (Float64))
(declare-fun sf4 () (Float128))

(declare-fun lf1 () (_ FloatingPoint 5 11))
(declare-fun lf2 () (_ FloatingPoint 8 24))
(declare-fun lf3 () (_ FloatingPoint 11 53))
(declare-fun lf4 () (_ FloatingPoint 15 113))

(assert (and (= sf1 lf1) (fp.eq sf1 lf1)))
(assert (and (= sf2 lf2) (fp.eq sf2 lf2)))
(assert (and (= sf3 lf3) (fp.eq sf3 lf3)))
(assert (and (= sf4 lf4) (fp.eq sf4 lf4)))

(check-sat)
(check-sat-using smt)
