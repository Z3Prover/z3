
; Copyright (c) 2015 Microsoft Corporation
(declare-fun p (Int) Bool)
(declare-const a Int)
(declare-const b Int)
(set-option :auto-config false)
(set-option :smt.mbqi false)

(assert (forall ((x Int) (y Int)) (! (p (+ x y 2)) :pattern (p (+ x y 2)))))
(assert (p (+ a 2)))

(check-sat)

(reset)
(set-option :auto-config true)
(declare-fun p (Int) Bool)
(declare-const a Int)
(declare-const b Int)

(assert (forall ((x Int) (y Int)) (! (p (+ x y 2)) :pattern (p (+ x y 2)))))
(assert (p (+ a 2)))

(check-sat)
