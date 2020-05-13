
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(set-option :pp.decimal true)
(declare-const x Real)
(declare-const y Real)
(declare-const a Int)
(declare-const b Int)

(simplify (tan (+ x (* pi (to_real a)) y)))

(simplify (tan (+ x (* pi 3 (to_real a)) y)))

(simplify (tan (+ x (* pi 3 (to_real a)) y (* (- 5) pi (to_real b)))))

(simplify (tan (+ x pi)))

(simplify (tan (- x pi)))

(simplify (tan (+ x (* 2 pi))))

(simplify (tan (- x (* 2 pi))))

(simplify (tan (+ x (/ pi 2))))
