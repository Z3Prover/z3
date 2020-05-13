
; Copyright (c) 2015 Microsoft Corporation



(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(set-option :produce-models true)

(assert (= (+ (* 2.0 a) (* 3.0 b) (* 2.0 c)) 10.0))
(assert (>= c a))
(assert (>= c b))

(apply (and-then simplify solve-eqs) :print-model-converter false)

(assert (= (+ c b) 0.0))

(apply (and-then simplify solve-eqs) :print-model-converter false)

(apply (and-then simplify (! solve-eqs :theory-solver false)) :print-model-converter false)

(reset)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(set-option :produce-models true)

(assert (= (+ (* 2 a) (* 3 b) (* 2 c)) 10))
(assert (>= c a))
(assert (>= c b))

(apply (and-then simplify solve-eqs) :print-model-converter false)

(assert (= (+ c b a) 1))

(apply (and-then simplify solve-eqs) :print-model-converter false)

(reset)

(declare-const a Int)
(declare-const b Int)
(declare-fun f (Int) Int)

(set-option :produce-models true)

(assert (= (+ a (f a)) 20))

(apply (and-then simplify solve-eqs) :print-model-converter false)

(assert (= (+ a (f a) b) 20))
(assert (>= b 10))
(apply (and-then simplify solve-eqs) :print-model-converter false)


