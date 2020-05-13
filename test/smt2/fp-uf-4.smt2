
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status sat)

(declare-fun my_uf_bf (Bool) Float32)
(assert (= (_ +zero 8 24) (my_uf_bf true)))
(assert (= (_ -zero 8 24) (my_uf_bf false)))

(check-sat)
(check-sat-using smt)
(exit)
