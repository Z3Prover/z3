
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

(declare-sort A)
(declare-sort B)
(declare-fun f (A) B)
(assert (forall ((x A) (y A))
                (! (=> (= (f x) (f y)) (= x y))
                   :pattern ((f x) (f y))
                   )))
(declare-const a1 A)
(declare-const a2 A)
(declare-const b B)
(assert (not (= a1 a2)))
(assert (= (f a1) b))
(assert (= (f a2) b))
(check-sat)

        
