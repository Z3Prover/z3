(declare-const x (Array Bool Int))
(assert (forall ((v (Array Bool Int))) (distinct 0 (select (store x (= x v) 0) false))))
(check-sat-using qsat)