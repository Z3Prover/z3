
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)
(declare-const x5 Real)
(declare-const x6 Real)
(declare-const x7 Real)
(declare-const x8 Real)
(assert
  (and
   (= (+ (* x1 x1) x2) 0.0)
   (= x2 (+ x3 1.0))
   (= x2 (+ x6 x7))
   (= x7 (+ x8 1.0))
   (<= x1 20.0)
   (<= x3 10.0)
   (<= x6 2.0)
   (<= x8 10.0)
   (<= x5 (* 2.0 x4))
   ))
(check-sat)
(eval (= x2 (+ x3 1.0)))
(eval (= x2 (+ x6 x7)))
(eval (= x7 (+ x8 1.0)))

