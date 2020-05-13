; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger; github issue #337.")

(declare-fun X () (_ FloatingPoint 11 53))
(declare-fun Y () (_ FloatingPoint  8 24))

(assert (fp.eq X (fp #b0 #b00000000000 #x0000000000001)))
(assert (fp.eq Y ((_ to_fp 8 24) RNE X)))
(assert (and
			(not (= Y (_ +zero 8 24)))
			(not (= Y (_ -zero 8 24)))))

(check-sat)
(exit)
