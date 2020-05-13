
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)

(simplify (cos 0))
(simplify (cos pi))
(simplify (cos (* 2 pi)))
(simplify (cos (* 3 pi)))
(simplify (cos (/ pi 2)))
(simplify (cos (+ pi pi (/ pi 2))))
(simplify (cos (* 3 (/ pi 2))))
(simplify (cos (- (+ (* 2 pi) (/ pi 2)))))
(simplify (cos (/ pi 6)))
(simplify (cos (* (/ 5 6) pi)))
(simplify (cos (* (/ 7 6) pi)))
