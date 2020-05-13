(declare-fun a () (Array Int (Array Int Int)))
(assert (= a (store a 0 (store (select a 0) 0 0))))
(check-sat-using qsat)