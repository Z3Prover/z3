(declare-const x Bool)
(assert (xor (not (not x)) x))
(check-sat)
