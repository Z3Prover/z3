; Partial application: pipeline operator
(set-logic HO_ALL)
(define-fun pipe ((x Int) (f (-> Int Int))) Int (f x))
(assert (not (= (pipe 5 (lambda ((x Int)) (* x x))) 25)))
(check-sat)
(exit)
