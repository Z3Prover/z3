; HO quantification: second-order induction schema
(set-logic HO_ALL)
(assert (not (forall ((P (-> Int Bool)))
  (=> (and (P 0) (forall ((n Int)) (=> (and (>= n 0) (P n)) (P (+ n 1)))))
      (forall ((n Int)) (=> (>= n 0) (P n)))))))
(check-sat)
(exit)
