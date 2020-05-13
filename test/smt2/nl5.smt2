
; Copyright (c) 2015 Microsoft Corporation
(declare-const x1 Real)
(declare-const x2 Real)
(assert
  (and
   (> x1 0.0)
   (> x2 0.0)
   (< (* x1 x2) 0.0)
   ))
(check-sat)

(reset)
(set-option :auto-config true)
(declare-const x1 Real)
(declare-const x2 Real)
(assert
  (and
   (> x1 0.0)
   (> x2 0.0)
   (< (* x1 x2) 0.0)
   ))
(check-sat)

