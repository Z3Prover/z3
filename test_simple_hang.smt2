(define-funs-rec ((simple ((x Int)) Int)) ((ite (= x 0) 0 (simple (- x 1)))))
(assert (= (simple 1) 0))