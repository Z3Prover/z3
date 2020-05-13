(set-option :model_validate true)
(declare-fun a () Real)
(assert (= a 1))
(check-sat-using (then qffd smt))