
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
   (= (+ (* x1 x1) x2) 2.0)
   (<= x2 x3)
   (<= x3 x2)
   (<= x3 x4)
   (<= x4 x3)
   (<= x4 x5)
   (<= x5 x4)
   (<= 0.0 x2)
   (<= x2 10.0)
   ))
(check-sat)
