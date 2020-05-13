(assert (exists ((a Int)) false))
(assert (forall ((b Int)) false))
(check-sat-using nnf)