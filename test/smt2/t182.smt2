
; Copyright (c) 2015 Microsoft Corporation


(set-option :pp.max-depth 100)

(set-logic QF_UFLIA)
(declare-const a Int)
(declare-const b Int)
(declare-fun f (Int) Int)

(assert (= b (+ (f a) 1)))
(assert (>= (f b) a))
(assert (>= (f (f (f (f (f (f (f (f (f a))))))))) (f a)))

(apply (and-then simplify solve-eqs) :print-benchmark true :print false)

