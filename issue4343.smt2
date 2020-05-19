(declare-fun a () String)
(assert (= (str.to.int a) 1))
(check-sat)
(get-model)