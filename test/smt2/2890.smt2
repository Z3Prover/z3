(set-option :model_validate true)
(declare-fun a () Int)
(declare-fun b () Real)
(assert (= b (/ 0 a)))
(assert (> b 0))
(check-sat)
