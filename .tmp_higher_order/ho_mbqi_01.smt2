; MBQI-Enum: find a function satisfying arithmetic constraint
; Solver must enumerate lambda candidates
(set-logic HO_ALL)
(assert (exists ((f (-> Int Int)))
  (and (= (f 0) 1)
       (= (f 1) 2)
       (= (f 2) 3))))
(check-sat)
(exit)
