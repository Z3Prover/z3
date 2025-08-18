(define-funs-rec ((g ((a Int) (b Int)) Bool)) ((or (= a b) (ite (> a b) (g (- a 1) b) (g a (- b 1))))))
(assert (g 2 2))
(check-sat)