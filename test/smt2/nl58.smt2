
; Copyright (c) 2015 Microsoft Corporation
(echo "buggy")
(declare-const x Int)
(declare-const y Real)
(assert 
  (and
   (<= 0 x)
   (<= (- 1.0) y)
   (< (+ (* (to_real x) y) (to_real x)) 0.0)
))
;; (check-sat)
;; TODO: fix this example without breaking Z3.
;; Z3 returns unknown.
;; The problem is that the crossnested form computation is disabled for mixed integer problems.
;; This modification is the code was motivated by a Formula bug. I have to find this bug report.
