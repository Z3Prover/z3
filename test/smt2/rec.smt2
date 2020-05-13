(define-fun-rec f ((x Int) (y Bool)) Int
    (if y (f (+ x 1) (not y)) x))

(define-funs-rec 
   ((ping ((x Int) (y Bool)) Int)
    (pong ((a Int) (b Int)) Bool))

   ((if y (ping (+ x 1) (pong x x)) x)
    (if (> a b) (ping a (pong b b)) b)))

(assert (< (f 0 true) 0))
(check-sat)