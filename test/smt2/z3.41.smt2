
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

(declare-sort A)
(declare-sort B)
(declare-fun f (A) B)
(declare-fun f-inv (B) A)
(assert (forall ((x A))
                (! (= (f-inv (f x)) x)
                   :pattern ((f x))
                   )))
(declare-const a1 A)
(declare-const a2 A)
(declare-const b B)
(assert (not (= a1 a2)))
(assert (= (f a1) b))
(assert (= (f a2) b))
(check-sat)

        
