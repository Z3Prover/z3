
; Copyright (c) 2015 Microsoft Corporation



(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-fun f (Int) Int)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)

(set-option :pp.max-depth 20)

(assert (or (= x1 0) 
            (= (f x2) (f x1))
            (and (p (f x2)) (= x2 3) (or (q (f x2)) (= (f (+ x2 1)) (f x1))))
            (and (p (f x2)) (>= (f x2) 0))
            (>= (ite (not (= x1 2)) x1 (+ x1 1)) x2)))

(apply (and-then simplify ctx-simplify))