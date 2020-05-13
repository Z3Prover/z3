
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 11 53))
(declare-fun Y () (_ FloatingPoint 11 53))

(assert (fp.leq X Y))
(assert (not (fp.geq X Y)))

(check-sat)
(check-sat-using smt)
(exit)
