; Advanced: continuation-passing style
(set-logic HO_ALL)
(define-fun add_cps ((x Int) (y Int) (k (-> Int Int))) Int
  (k (+ x y)))
(define-fun mul_cps ((x Int) (y Int) (k (-> Int Int))) Int
  (k (* x y)))
; compute (3 + 4) * 2 in CPS
(assert (not (= (add_cps 3 4 (lambda ((sum Int)) (mul_cps sum 2 (lambda ((r Int)) r)))) 14)))
(check-sat)
(exit)
