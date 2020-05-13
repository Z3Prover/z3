
; Copyright (c) 2015 Microsoft Corporation
(set-option :pp.max-depth 100)
(declare-fun p (Int) Bool)
(declare-fun f (Int Real) Bool)
(declare-fun q (Int Bool) Bool)
(declare-fun a () Int)

(push)
(assert (! (p 0) :lblpos foo :lblpos baa :lblneg tst :lblneg tst2))
(apply snf)
(echo "-----")
(pop)


(push)
(assert (not (! (p 0) :lblpos foo :lblpos baa :lblneg tst :lblneg tst2)))
(apply snf)
(echo "-----")
(pop)

