
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(assert
  (and
   (> (- (* x1 x2) x3) 0)
   (= x1 1)
   (= x2 x3)
   ))
(check-sat)

(reset)
(set-logic QF_NIA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(assert
  (and
   (> (- (* x1 x2) x3) 0)
   (= x1 1)
   (= x2 x3)
   ))
(check-sat)


