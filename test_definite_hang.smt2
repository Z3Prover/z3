(define-funs-rec ((loop ((x Int)) Int)) ((loop x)))
(assert (= (loop 1) 0))