
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status sat)

(declare-fun my_uf_fb (Float32) Bool)
(assert (= false (my_uf_fb (_ +oo 8 24))))
(assert (= true (my_uf_fb (_ -oo 8 24))))

(check-sat)
(check-sat-using smt)
(exit)
