; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger; github issue #337.")

(declare-fun X () (_ FloatingPoint 11 53))
(declare-fun Y () (_ FloatingPoint  8 24))

(assert (fp.eq X (fp #b0 #b10001111110 #xFFFFFE0000000)))
(assert (fp.eq Y ((_ to_fp 8 24) RNE X)))

(assert (not (= Y (fp #b0 #xfe #b11111111111111111111111))))

(check-sat)
(exit)

