
; Copyright (c) 2015 Microsoft Corporation

(declare-const a Int)
(declare-const b Int)

(set-option :pp.flat-assoc false)

(simplify (- 8 4 1))
(display (- 8 4 1))
(display (- a b 10 a))
(display (- 8.0 4.0 1.0))

