
; Copyright (c) 2015 Microsoft Corporation
(set-option :pp.max-depth 100)

(declare-const a Real)

(assert (forall ((x Int) (y Real)) (=> (= (mod x 3) 0) (= (/ y a) 0))))
(apply purify-arith)

(reset)

(assert (forall ((x Int)) (= (mod x 3) 0)))
(apply purify-arith)

(reset)

(assert (forall ((x Int)) (<= (+ (* x x 3) x) 2)))
(apply purify-arith)

(reset)

(declare-const a Real)
(declare-const b Real)

(assert (= (/ a b) 0))

(apply purify-arith)
