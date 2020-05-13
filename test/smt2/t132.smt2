
; Copyright (c) 2015 Microsoft Corporation


(set-logic QF_AUFLIA)

(declare-fun x () Int)
(declare-fun y () Real)
(declare-fun a () (Array Int Int))
(declare-fun bv () (_ BitVec 32))
(declare-fun f (Int) Int)
(declare-fun y () Int)

(assert (= (* x x) 2))
(assert (= (* 2 x 3) (+ y 2 y)))
(assert (>= (div 2 x) 3))
(assert (forall ((x Int)) (= (f x) x)))
