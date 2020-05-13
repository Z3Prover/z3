
; Copyright (c) 2015 Microsoft Corporation
(set-option :pp.decimal true)
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(assert
  (and
   (> x1 0.0)
   (> x2 0.0)
   (> (* x1 x2) 0.)
   ))
(check-sat)

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(assert
  (and
   (> x1 0.0)
   (> x2 0.0)
   (> (* x1 x2) 0.)
   ))
(check-sat)



