
; Copyright (c) 2015 Microsoft Corporation
(set-option :pp.max-depth 100)
(declare-fun p (Int) Bool)
(declare-fun f (Int Real) Bool)
(declare-fun q (Int Bool) Bool)
(declare-fun a () Int)

(push)
(assert (q 10 (! (p 0) :lblpos foo :lblneg tst)))
(apply snf)
(echo "-----")
(pop)


(push)
(assert (q 10 (and (! (p 0) :lblpos foo) (! (p 1) :lblneg tst))))
(apply snf)
(echo "-----")
(apply nnf)
(echo "-----")
(pop)
