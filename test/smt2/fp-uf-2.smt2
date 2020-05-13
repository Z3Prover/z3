
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-option :model_validate true)

(declare-fun f (Int) (_ FloatingPoint 53 11))

(assert (= (f 1) (_ +oo 53 11)))
(assert (= (f 2) (_ -oo 53 11)))

(check-sat)
(check-sat-using smt)
(exit)
