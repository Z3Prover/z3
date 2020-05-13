;; Copyright (c) 2017 Nathan Fulton
(declare-const _yy Real)
(declare-const _xx Real)
(declare-const _Y Real)
(declare-const _X Real)
(declare-const _x Real)
(declare-const _y Real)
(declare-const _z Real)

(assert (not (=> (and (and (and (<= _xx _x) (<= _x _X)) (and (<= _yy _y) (<= _y _Y))) (and (or (< _Y 0) (< 0 _yy)) (and (<= (/ _xx _yy) _z) (and (<= (/ _xx _Y) _z) (and (<= (/ _X _yy) _z) (<= (/ _X _Y) _z)))))) (<= (/ _x _y) _z))))
(check-sat)
