
; Copyright (c) 2015 Microsoft Corporation

(set-option :smt.mbqi true)
(declare-fun f (Real) Real)
(declare-fun g (Real) Real)
(declare-const a Real)
(assert (forall ((x Real)) (=> (and (<= 0.0 x) (<= x 2.0)) (= (f (g x)) 1.0))))
(assert (= (f (g a)) 2.0))
(check-sat)

