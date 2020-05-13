
; Copyright (c) 2015 Microsoft Corporation
(echo "ABSolver benchmark")
(set-option :produce-models true)
(declare-const a Int)
(declare-const b Int)
(assert 
  (and
   (> a 0)
   (> b 0)
   (< a 5)
   (< b 5)
   (< (div a b) 3)
))
(check-sat)

(exit) ;; Investigate why the following configuration returns unknown...

(reset)
(set-logic QF_NIA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const a Int)
(declare-const b Int)
(assert 
  (and
   (> a 0)
   (> b 0)
   (< a 5)
   (< b 5)
   (< (div a b) 3)
))
(check-sat)
(get-model)