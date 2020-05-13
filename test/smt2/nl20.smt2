
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(assert
  (and
   (= (* x1 x1 x2) 1.0)
   (= (* x1 x2 x2) x2)
   (= (* x1 x2) x2)
   (not (= x2 1.0))
   ))
(check-sat)
(exit)
; The following example crashes Z3

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(assert
  (and
   (= (* x1 x1 x2) 1.0)
   (= (* x1 x2 x2) x2)
   (= (* x1 x2) x2)
   (not (= x2 1.0))
   ))
(check-sat)



