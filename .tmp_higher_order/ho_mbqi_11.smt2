; MBQI-Enum: SyGuS-style function synthesis
; Find f such that f(x) >= x and f(x) <= x+1
(set-logic HO_ALL)
(assert (exists ((f (-> Int Int)))
  (forall ((x Int)) (and (>= (f x) x) (<= (f x) (+ x 1))))))
(check-sat)
(exit)
