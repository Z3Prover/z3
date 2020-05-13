(assert (exists ((a Bool)) false))
(assert (not false))
(check-sat-using purify-arith)