
; Copyright (c) 2015 Microsoft Corporation


(set-option :pp.max-depth 100)
(declare-fun p (Int) Bool)
(declare-fun f (Int Real) Bool)

(push)
(assert (not (forall ((x Int) (z Real) (z2 Int)) (=> (and (f x z) (f z2 z)) (exists ((y Int)) (and (not (= y x)) (f y z)))))))
(apply nnf)
(pop)


(push)
(assert (not (forall ((x Int) (z Real) (z2 Int)) (! (=> (and (f x z) (f z2 z)) (exists ((y Int)) (and (not (= y x)) (f y z)))) :skolemid foo))))
(apply nnf)
(pop)
