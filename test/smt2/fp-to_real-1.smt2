
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unknown) ; nlsat may give up due to non-linear encoding of to_fp
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-const X (_ FloatingPoint 5 11))
(declare-const R Real)

(assert (= X ((_ to_fp 5 11) RTZ R)))
(assert (= R (fp.to_real X)))

(check-sat)
(check-sat-using smt)
(exit)
