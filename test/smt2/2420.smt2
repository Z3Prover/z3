(declare-fun q (Int) Int)
(check-sat)
(get-model)
(get-value (q))