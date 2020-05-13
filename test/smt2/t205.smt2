
; Copyright (c) 2015 Microsoft Corporation

(simplify #xff)
(simplify #xfe)
(set-option :pp.bv-neg true)
(simplify #xff)
(simplify #xfe)
(set-option :pp.bv-literals false)
(simplify #xff)
(simplify #xfe)

(simplify (/ 1.0 3.0))
(simplify 2.0)
(simplify 2)
(set-option :pp.decimal true)
(simplify (/ 1.0 3.0))
(simplify 2.0)
(simplify 2)
(set-option :pp.decimal-precision 20)
(simplify (/ 1.0 3.0))
(simplify 2.0)
(simplify 2)
