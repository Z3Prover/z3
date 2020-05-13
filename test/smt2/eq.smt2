
; Copyright (c) 2015 Microsoft Corporation


(declare-const a Int)
(declare-fun f (Int) Int)
(simplify (f f))
(simplify (a + 1))
(assert (a = 1))
