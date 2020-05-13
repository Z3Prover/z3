
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)
(declare-const x5 Real)
(assert
  (and
      (< (+ (* x1 x1 x3 x3 x3 x3) (* (- 2.0) x1 x2 x3 x3 x4) (* x2 x2 x4 x4)) x5)
      (< x5 0.0)
   ))
(check-sat)
(exit)
;; Z3 returns wrong answer with AUTO_CONFIG=true

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(set-option :pp.max-depth 100)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)
(declare-const x5 Real)
(assert
  (and
      (< (+ (* x1 x1 x3 x3 x3 x3) (* (- 2.0) x1 x2 x3 x3 x4) (* x2 x2 x4 x4)) x5)
      (< x5 0.0)
   ))
(check-sat)
(get-model)


