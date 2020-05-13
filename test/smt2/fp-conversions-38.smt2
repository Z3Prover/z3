; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger; github issue #337.")

(declare-fun X () (_ FloatingPoint 11 53))
(declare-fun Y () (_ FloatingPoint 9 53))

(assert (fp.eq X (fp #b0 #b10011111110 #xFFFFFFFFFFFFF)))
(assert (= Y ((_ to_fp 9 53) RNE X)))
(assert (not (= Y (fp #b0 #b111111110 #xfffffffffffff))))

(check-sat)
(exit)
