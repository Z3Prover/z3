(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(assert
 (or
  (forall ((e Real))
   (and (or (>= (/ a d) 12.0) (>= (+ a d) (+ 5.0 c)) (>= (+ 5.0 c) 0.0))
    (>= (- b) 12.0)))
  (exists ((g Real)) (forall ((f Real)) (exists ((h Real)) true)))))
(check-sat-using (then qe smt))