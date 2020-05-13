
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

(set-option :smt.mbqi true)
(declare-sort S)
(declare-fun g (S S) S)
(declare-fun f (S S) S)
(declare-const a S)
(declare-const b S)

(assert (forall ((x S) (y S))
                (= (g (f x y) (f x x)) x)))
(assert (forall ((x S) (y S))
                (= (f (g x y) (g x x)) x)))
(assert (forall ((x S) (y S) (z S))
                (= (g (g x y) z) (g (g y z) x))))
(assert (forall ((x S) (y S) (z S))
                (= (f (f x y) z) (f (f y z) x))))
(assert (distinct (g a (f b a)) (f a (g b a))))
(check-sat)
