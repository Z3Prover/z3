
; Copyright (c) 2015 Microsoft Corporation


(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)

(simplify (distinct x1 x2 x3 x4)
          :blast-distinct true)
(simplify (distinct x1 x2 x3 x4)
          :blast-distinct true
          :elim-and true)
(simplify (distinct x1 (+ x1 1) x3 x4)
          :blast-distinct true)