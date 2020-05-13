
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(declare-const x Real)
(assert (>= x 0.0))
(assert (not (= (^ (* 2.0 x) (/ 1.0 2.0))
                (* (^ 2.0 (/ 1.0 2.0))
                   (^ x (/ 1.0 2.0))))))
(check-sat)

        