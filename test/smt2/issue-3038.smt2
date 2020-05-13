(declare-fun a () Real)
(assert (distinct (^ a 0.0) 1.0))
(check-sat-using nlqsat)