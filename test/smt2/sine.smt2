
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)

(simplify (sin 0))
(simplify (sin pi))
(simplify (sin (* 2 pi)))
(simplify (sin (* 3 pi)))
(simplify (sin (/ pi 2)))
(simplify (sin (+ pi pi (/ pi 2))))
(simplify (sin (* 3 (/ pi 2))))
(simplify (sin (- (+ (* 2 pi) (/ pi 2)))))
(simplify (sin (/ pi 6)))
(simplify (sin (* (/ 5 6) pi)))
(simplify (sin (* (/ 7 6) pi)))
