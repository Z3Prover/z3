
; Copyright (c) 2015 Microsoft Corporation


(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 4))

(simplify (bvsle b #x5))
(simplify (bvule b #x5))
(simplify (bvule b (concat #b00 #b00)))
(simplify (bvule a #x00000000))
(simplify (bvule a #x00001e80))
(simplify (bvsle a #x00001e80))
(simplify (bvule #x00001e80 a))
