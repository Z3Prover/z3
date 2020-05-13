
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 11 53))
(assert (= X (_ +zero 11 53)))

(check-sat)
(check-sat-using smt)
(exit)
