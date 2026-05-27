; MBQI-Enum: predicate synthesis
(set-logic HO_ALL)
(assert (exists ((P (-> Int Bool)))
  (and (P 2) (P 4) (P 6) (not (P 1)) (not (P 3)))))
(check-sat)
(exit)
