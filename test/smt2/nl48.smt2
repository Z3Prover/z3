
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(assert
  (and
   (= x2 (+ x3 x4))
   (not (= (* x1 x2) (+ (* x1 x3) (* x1 x4))))
   ))
(check-sat)

(reset)
(set-logic QF_NIA)
(set-option :produce-models true)
(set-option :auto-config true)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(assert
  (and
   (= x2 (+ x3 x4))
   (not (= (* x1 x2) (+ (* x1 x3) (* x1 x4))))
   ))
(check-sat)
