
; Copyright (c) 2015 Microsoft Corporation
(set-option :smt.arith.nl false) ;; Z3 should prove this benchmark even when nonlinear support is disabled.
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert (and
   (>= (* x1 x2 x3) 1.0)
   (<= x2 0.0)
   (>= x2 0.0)
   ))
(check-sat)

(reset)
(set-option :smt.arith.nl true)
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert (and
   (>= (* x1 x2 x3) 1.0)
   (<= x2 0.0)
   (>= x2 0.0)
   ))
(check-sat)

(reset)
(set-logic QF_NRA)
(set-option :produce-models true)
(set-option :auto-config true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert (and
   (>= (* x1 x2 x3) 1.0)
   (<= x2 0.0)
   (>= x2 0.0)
   ))
(check-sat)
         