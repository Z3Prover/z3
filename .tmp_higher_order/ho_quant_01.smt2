; HO quantification: existential over functions
; Requires MBQI-Enum to find witness lambda
(set-logic HO_ALL)
(assert (not (exists ((f (-> Int Int))) (forall ((x Int)) (= (f x) (+ x 1))))))
(check-sat)
(exit)
