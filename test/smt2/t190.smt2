
; Copyright (c) 2015 Microsoft Corporation
(set-option :pp.max-depth 100)
(declare-fun p (Int) Bool)
(declare-fun f (Int Real) Bool)
(declare-fun q (Int Bool) Bool)
(declare-fun a () Int)

(push)
(assert (= (ite (> (ite (! (p 0) :lblneg baa) 20 30) a) 0 1) a))
(apply snf)
(echo "----")
(pop)

(push)
(assert (= (ite (> (ite (! (p 0) :lblpos baa) 20 30) a) 0 1) a))
(apply snf)
(echo "----")
(pop)
