; Choice term: choice with arithmetic constraint
(set-logic HO_ALL)
(define-fun sqrt_approx ((n Int)) Int
  (choice ((x Int)) (and (>= x 0) (<= (* x x) n) (> (* (+ x 1) (+ x 1)) n))))
(assert (not (let ((s (sqrt_approx 10)))
  (and (>= s 0) (<= (* s s) 10) (> (* (+ s 1) (+ s 1)) 10)))))
(check-sat)
(exit)
