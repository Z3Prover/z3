
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_LRA)
(declare-fun v0 () Real)
(declare-fun v1 () Real)
(declare-fun v2 () Real)
(assert (let ((e3 11))
(let ((e4 0))
(let ((e5 1))
(let ((e6 (/ e5 (~ e3))))
(let ((e7 (+ v0 v1)))
(let ((e8 (+ e6 e7)))
(let ((e9 (* v2 e4)))
(let ((e10 (<= v2 v1)))
(let ((e11 (> e6 e6)))
(let ((e12 (<= v2 e9)))
(let ((e13 (= e9 e9)))
(let ((e14 (<= e8 e7)))
(let ((e15 (distinct v0 v0)))
(let ((e16 (ite e11 e8 e8)))
(let ((e17 (ite e12 e9 v1)))
(let ((e18 (ite e14 e6 e7)))
(let ((e19 (ite e13 e16 e8)))
(let ((e20 (ite e10 v0 e6)))
(let ((e21 (ite e14 v2 e16)))
(let ((e22 (ite e15 e16 e9)))
(let ((e23 (> e21 e8)))
(let ((e24 (<= e22 e19)))
(let ((e25 (< e9 e8)))
(let ((e26 (= e18 e8)))
(let ((e27 (= e7 e7)))
(let ((e28 (distinct e22 e18)))
(let ((e29 (= e19 e6)))
(let ((e30 (> e18 v2)))
(let ((e31 (= e8 v0)))
(let ((e32 (distinct e7 e17)))
(let ((e33 (< e19 e7)))
(let ((e34 (= e8 v0)))
(let ((e35 (= e8 v2)))
(let ((e36 (distinct e16 v1)))
(let ((e37 (>= e16 e20)))
(let ((e38 (and e13 e34)))
(let ((e39 (xor e32 e27)))
(let ((e40 (xor e15 e36)))
(let ((e41 (=> e39 e29)))
(let ((e42 (= e37 e35)))
(let ((e43 (and e28 e30)))
(let ((e44 (=> e23 e14)))
(let ((e45 (xor e42 e26)))
(let ((e46 (not e11)))
(let ((e47 (or e33 e41)))
(let ((e48 (and e24 e44)))
(let ((e49 (ite e25 e10 e10)))
(let ((e50 (and e47 e40)))
(let ((e51 (=> e46 e31)))
(let ((e52 (xor e43 e50)))
(let ((e53 (not e38)))
(let ((e54 (=> e53 e53)))
(let ((e55 (= e48 e48)))
(let ((e56 (xor e54 e49)))
(let ((e57 (not e52)))
(let ((e58 (ite e12 e45 e57)))
(let ((e59 (=> e55 e51)))
(let ((e60 (=> e59 e58)))
(let ((e61 (and e60 e60)))
(let ((e62 (=> e56 e56)))
(let ((e63 (or e62 e62)))
(let ((e64 (not e61)))
(let ((e65 (and e63 e64)))
e65
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
