
; Copyright (c) 2015 Microsoft Corporation

(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-fun f (Int Int Int) Int)
(declare-fun g (Int) Int)
(declare-const b Bool)

(set-option :pp.max-depth 1000)

(push)
(assert (= x1 (g x2)))
(assert (= x2 (g x3)))
(assert (= x3 (f x1 x2 x3)))
(apply solve-eqs)
(pop)


(push)
(assert (= x1 (g x2)))
(assert (= x2 (g x3)))
(assert (ite b (= x3 (g x2)) (= x3 (f x1 x2 x3))))
(apply solve-eqs)
(pop)

(push)
(assert (= x1 (g x2)))
(assert (= x2 (g x3)))
(assert (ite b (= x3 (f x1 x2 x3)) (= x3 (g x2))))
(apply solve-eqs)
(pop)

(push)
(assert (= x1 (g x2)))
(assert (= x2 (g x3)))
(assert (ite (= x3 (g x1)) (= x3 (g x2)) (= x3 (g (g x1)))))
(apply solve-eqs)
(pop)

(push)
(assert (= (+ x1 x2) 1))
(assert (= (+ x2 x3) 2))
(assert (= (+ x3 x2 x1 (g x3)) 3))
(apply solve-eqs)
(pop)

(push)
(assert (= (+ x1 x2) 1))
(assert (= (+ x2 x3) 2))
(assert (= (+ x3 x2 x1) (g x3)))
(apply solve-eqs)
(pop)