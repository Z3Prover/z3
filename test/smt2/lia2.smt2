
; Copyright (c) 2015 Microsoft Corporation
(set-info :smt-lib-version 2.0)
(assert (forall (( x Int)) (forall ((y Int)) (= y x))))
(check-sat)
