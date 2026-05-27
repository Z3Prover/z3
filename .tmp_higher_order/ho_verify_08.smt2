; Verification: weakest precondition
(set-logic HO_ALL)
(define-fun wp_assign ((post (-> Int Bool)) (e (-> Int Int)) (x Int)) Bool
  (post (e x)))
; x := x + 1; requires x >= 0 to ensure x >= 1 after
(assert (not (forall ((x Int))
  (=> (>= x 0)
      (wp_assign (lambda ((v Int)) (>= v 1))
                 (lambda ((v Int)) (+ v 1))
                 x)))))
(check-sat)
(exit)
