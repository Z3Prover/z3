
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)

(define-fun my-cos ((x Real)) Real
  (cos (- x (* 2 pi))))

(simplify (my-cos (* (/ 1 4) pi)))
(simplify (my-cos (* (/ 3 4) pi)))
(simplify (my-cos (* (/ 5 4) pi)))
(simplify (my-cos (* (/ 7 4) pi)))
(echo "....")
(simplify (my-cos (* (/ 1 3) pi)))
(simplify (my-cos (* (/ 2 3) pi)))
(simplify (my-cos (* (/ 4 3) pi)))
(simplify (my-cos (* (/ 5 3) pi)))
(echo "....")
(simplify (my-cos (* (/ 1 12) pi)))
(simplify (my-cos (* (/ 11 12) pi)))
(simplify (my-cos (* (/ 13 12) pi)))
(simplify (my-cos (* (/ 23 12) pi)))
(echo "....")
(simplify (my-cos (* (/ 5 12) pi)))
(simplify (my-cos (* (/ 7 12) pi)))
(simplify (my-cos (* (/ 17 12) pi)))
(simplify (my-cos (* (/ 19 12) pi)))

(echo "umy-cosg decimals")

(set-option :pp.decimal true)
(simplify (my-cos (* (/ 1 4) pi)))
(simplify (my-cos (* (/ 3 4) pi)))
(simplify (my-cos (* (/ 5 4) pi)))
(simplify (my-cos (* (/ 7 4) pi)))
(echo "....")
(simplify (my-cos (* (/ 1 3) pi)))
(simplify (my-cos (* (/ 2 3) pi)))
(simplify (my-cos (* (/ 4 3) pi)))
(simplify (my-cos (* (/ 5 3) pi)))
(echo "....")
(simplify (my-cos (* (/ 1 12) pi)))
(simplify (my-cos (* (/ 11 12) pi)))
(simplify (my-cos (* (/ 13 12) pi)))
(simplify (my-cos (* (/ 23 12) pi)))
(echo "....")
(simplify (my-cos (* (/ 5 12) pi)))
(simplify (my-cos (* (/ 7 12) pi)))
(simplify (my-cos (* (/ 17 12) pi)))
(simplify (my-cos (* (/ 19 12) pi)))


