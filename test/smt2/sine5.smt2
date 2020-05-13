
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)
(declare-const y Real)
(declare-const a Int)

(simplify (sin (+ x (* 2 pi) y)))
(simplify (sin (+ x (* (- 2) pi) y)))
(simplify (sin (+ x (* 4 pi) y)))
(simplify (sin (+ x (* (- 4) pi) y)))
(echo "....")

(simplify (sin (+ x (* 1 pi) y)))
(simplify (sin (+ x (* (- 1) pi) y)))
(simplify (sin (+ x (* 3 pi) y)))
(simplify (sin (+ x (* (- 3) pi) y)))
(echo "....")

(simplify (sin (+ x (* (/ 1 2) pi) y)))
(simplify (sin (+ x (* 2 pi) (* (/ 1 2) pi) y)))
(simplify (sin (+ x (* (- 2) pi) (* (/ 1 2) pi) y)))
(simplify (sin (+ x (* (- 4) pi) (* (/ 1 2) pi) y)))
(echo "....")

(simplify (sin (+ x (* (/ 3 2) pi) y)))
(simplify (sin (+ x (* 2 pi) (* (/ 3 2) pi) y)))
(simplify (sin (+ x (* (- 2) pi) (* (/ 3 2) pi) y)))
(simplify (sin (+ x (* (- 4) pi) (* (/ 3 2) pi) y)))
