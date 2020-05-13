
; Copyright (c) 2015 Microsoft Corporation
;; Z3 fails when using just theory_arith.
;; The main problem is that theory_arith implementation is incomplete for non-linear arithmetic, and it does not have any model finding capabilities for 
;; QF_NRA benchmarks
;; However, it does have model finding capabilities for QF_NIA benchmarks.

(reset)
(set-option :auto-config false)
(set-option :produce-models true)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(assert
  (and
   (= (+ x1 x2) 1)
   (= (+ (* x1 x3) x2 (* (- 1) x3)) 2)
   (> x3 0)
   ))
(check-sat)


(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(set-option :pp.max-depth 100)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert
  (and
   (= (+ x1 x2) 1.0)
   (= (+ (* x1 x3) x2 (* (- 1.0) x3)) 2.0)
   (> x3 0)
   ))
(check-sat)
(exit)
;; The produced model is wrong...
(get-model)
(eval 
  (and
   (= (+ x1 x2) 1.0)
   (= (+ (* x1 x3) x2 (* (- 1.0) x3)) 2.0)
   (> x3 0)
   ))


