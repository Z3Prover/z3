(define-funs-rec ((a () Int) 
                  (b ((c Int)) Bool))
 (0 
 (ite (< c 0) false (ite (= c 0) true (b (- 2))))))
(assert (b 7))
(check-sat)