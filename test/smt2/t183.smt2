
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config false)

(set-option :pp.max-depth 100)
(declare-fun p (Int) Bool)
(declare-fun f (Int Real) Bool)

(push)
(assert (= (p 0) (and (p 1) (p 2))))
(assert (implies (p 3) (p 4)))
(assert (xor (p 5) (and (p 6) (p 7))))
(apply nnf)
(pop)

(echo "----")

(push)
(assert (ite (and (p 0) (p 1)) (p 2) (p 3)))
(apply nnf)
(pop)

(echo "----")
(push)
(assert (p (ite (p 1) 10 20)))
(apply nnf)
(pop)
