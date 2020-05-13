
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config false)
(set-option :smt.mbqi false)

(declare-fun ff ((Array Int Int)) (Array Int Int))
(assert (forall ((s (Array Int Int)) ) (! (= s (ff s)) :pattern (2))))
(assert (forall ((s (Array Int Int)) ) (! (= s (ff s)) :pattern ())))
(assert (forall ((s (Array Int Int)) ) (! (= s (ff s)) :pattern)))
(assert (forall ((s (Array Int Int)) ) (! (= s (ff s)) :pattern (1.0))))
(assert (forall ((s (Array Int Int)) ) (! (= s (ff s)) :pattern (=))))
(assert (forall ((s (Array Int Int)) ) (! (= s (ff s)) :pattern (s))))
(assert (forall ((s (Array Int Int)) ) (! (= s (ff s)) :pattern (ff s))))
(assert (forall ((s (Array Int Int)) ) (! (= (store s 0 0) (ff s)) :pattern 2)))
(assert (forall ((s (Array Int Int)) ) (! (= (store s 0 0) (ff s)) :pattern true)))

(apply simplify)
