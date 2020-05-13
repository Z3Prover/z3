
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(simplify (sin (+ x (* 2 pi) y (* 2 pi z))))
(simplify (sin (+ x (* 2 pi) y (* 4 pi z))))
(simplify (sin (+ x (* 2 pi) y (* pi z))))

