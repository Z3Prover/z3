(set-option :fp.xform.bit_blast true)
(assert (forall ((a Int)) (= a 0)))
;(check-sat)
(check-sat-using horn)