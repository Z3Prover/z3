
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config false) (set-option :smt.mbqi false) (declare-fun f (Int Int) Int)
(declare-fun a () Int)
(assert (forall ((x Int) (y Int)) (=> (and (= x (f y x))) (= y (f a (f y x)))) (= x y))))
(assert (forall ((x Int) (y Int)) (=> (and (= x (f y x)) (= y (f a (f y x)))) (= x y)))))
(check-sat)