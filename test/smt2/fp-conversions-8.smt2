
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 11 53))
(declare-fun R () Real)

; may return `unknown' because of translation to non-linear reals.
(assert (= R (fp.to_real X)))
(assert (<= R 3.5))
(assert (>= R 3.0))

(check-sat)
(check-sat-using smt)
(exit)
