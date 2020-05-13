
; Copyright (c) 2015 Microsoft Corporation


(declare-const x Int)
(declare-const z Int)

(assert (forall ((y Int)) (not (and (<= 0 y) (<= y x)))))
(assert (= z (+ x 1)))

(apply qe)