
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 11 53))
(declare-fun Y () (_ FloatingPoint 11 53))

(assert (= Y (fp.abs X)))
(assert (not (= X (_ -zero 11 53))))
(assert (not (= X (_ +zero 11 53))))
(assert (fp.isNegative X))

(check-sat)
(check-sat-using smt)
(exit)
