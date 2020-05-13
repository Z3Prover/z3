
; Copyright (c) 2015 Microsoft Corporation
(set-option :pp.max-depth 100)
(declare-fun p (Int) Bool)
(declare-fun f (Int Real) Bool)
(declare-fun q (Int Bool) Bool)
(declare-fun a () Int)

(push)
(assert (= (q 10 (and (forall ((x Int)) (p x)) (p 2))) (p 0)))
(apply snf)
(echo "-----")
(apply nnf)
(pop)

