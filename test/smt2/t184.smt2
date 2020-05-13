
; Copyright (c) 2015 Microsoft Corporation


(set-option :pp.max-depth 100)
(declare-fun p (Int) Bool)
(declare-fun f (Int Real) Bool)

(push)
(assert (forall ((x Int) (z Real) (z2 Int)) (=> (and (f x z) (f z2 z)) (exists ((y Int)) (and (not (= y x)) (f y z))))))
(apply nnf :print false :print-benchmark true)
(pop)

(echo "----")

