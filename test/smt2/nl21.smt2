
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert
  (and
   (> x1 0.0)
   (> x2 0.0)
   (> x3 0.0)
   (= (+ x1 x2) 1.0)
   (= (+ (* x1 x3) x2 (* (- 1.0) x3)) 2.0)
   ))
(check-sat)

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert
  (and
   (> x1 0.0)
   (> x2 0.0)
   (> x3 0.0)
   (= (+ x1 x2) 1.0)
   (= (+ (* x1 x3) x2 (* (- 1.0) x3)) 2.0)
   ))
(check-sat)



