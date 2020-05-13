
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config false)
(set-option :smt.mbqi false)

(declare-fun ff ((Array Int Int)) (Array Int Int))
(assert (forall ((s (Array Int Int)) ) (! (= s (ff s)) :pattern (= s (ff s)))))

(apply simplify)
