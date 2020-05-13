
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)

(define-fun my-sin ((x Real)) Real
  (sin (- x (* 2 pi))))

(simplify (my-sin (* (/ 1 4) pi)))
(simplify (my-sin (* (/ 3 4) pi)))
(simplify (my-sin (* (/ 5 4) pi)))
(simplify (my-sin (* (/ 7 4) pi)))
(echo "....")
(simplify (my-sin (* (/ 1 3) pi)))
(simplify (my-sin (* (/ 2 3) pi)))
(simplify (my-sin (* (/ 4 3) pi)))
(simplify (my-sin (* (/ 5 3) pi)))
(echo "....")
(simplify (my-sin (* (/ 1 12) pi)))
(simplify (my-sin (* (/ 11 12) pi)))
(simplify (my-sin (* (/ 13 12) pi)))
(simplify (my-sin (* (/ 23 12) pi)))
(echo "....")
(simplify (my-sin (* (/ 5 12) pi)))
(simplify (my-sin (* (/ 7 12) pi)))
(simplify (my-sin (* (/ 17 12) pi)))
(simplify (my-sin (* (/ 19 12) pi)))

(echo "using decimals")

(set-option :pp.decimal true)
(simplify (my-sin (* (/ 1 4) pi)))
(simplify (my-sin (* (/ 3 4) pi)))
(simplify (my-sin (* (/ 5 4) pi)))
(simplify (my-sin (* (/ 7 4) pi)))
(echo "....")
(simplify (my-sin (* (/ 1 3) pi)))
(simplify (my-sin (* (/ 2 3) pi)))
(simplify (my-sin (* (/ 4 3) pi)))
(simplify (my-sin (* (/ 5 3) pi)))
(echo "....")
(simplify (my-sin (* (/ 1 12) pi)))
(simplify (my-sin (* (/ 11 12) pi)))
(simplify (my-sin (* (/ 13 12) pi)))
(simplify (my-sin (* (/ 23 12) pi)))
(echo "....")
(simplify (my-sin (* (/ 5 12) pi)))
(simplify (my-sin (* (/ 7 12) pi)))
(simplify (my-sin (* (/ 17 12) pi)))
(simplify (my-sin (* (/ 19 12) pi)))


