; Higher-order: curried addition
(set-logic HO_ALL)
(define-fun cadd ((x Int)) (-> Int Int)
  (lambda ((y Int)) (+ x y)))
(assert (not (= ((cadd 3) 4) 7)))
(check-sat)
(exit)
