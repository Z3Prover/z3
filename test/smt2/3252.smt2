(set-logic NIA)
;(set-option :model_validate true)
(set-option :smt.arith.solver 6)
(assert (> (mod 0 0) 163))
(check-sat)
(exit)