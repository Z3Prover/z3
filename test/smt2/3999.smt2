(declare-fun a () String)
(declare-fun b () Int)
(assert (= (str.replace "A" (int.to.str b) a) "A"))
(check-sat)