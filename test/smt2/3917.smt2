(define-fun-rec a ((b Int)) Int 0)
(assert (= (a 0) 1))
(check-sat)