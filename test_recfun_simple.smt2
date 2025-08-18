(define-funs-rec ((f ((x Int)) Int)) ((ite (= x 0) 0 (+ 1 (f (- x 1))))))
(assert (= (f 2) 2))