
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)
(declare-const y Real)
(declare-const a Int)

(simplify (sin (+ x (* 2 pi) y (* 2 pi (to_real a)))))
(simplify (sin (+ x (* 2 pi) y (* 4 pi (to_real a)))))
(simplify (sin (+ x (* 2 pi) y (* (- 4) pi (to_real a)))))
(simplify (sin (+ x (* 2 pi) y (* (- 2) pi (to_real a)))))
(simplify (sin (+ x (* 2 pi) y (* pi (to_real a)))))

(simplify (sin (+ x (* 2 pi) y (* 2 (to_real a) pi))))
(simplify (sin (+ x (* 2 pi) y (* 4 (to_real a) pi))))

