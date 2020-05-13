
; Copyright (c) 2015 Microsoft Corporation


(declare-const a1 Int)
(declare-const a2 Int)
(declare-const a3 Int)

(display (= 1 2 3 4 5 6))
(display (= a1 a2 a3 a3))
(simplify (= a1 a2 a3 a3))

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(display (=> p1 p2 p3))
(simplify (=> p1 p2 p3))

