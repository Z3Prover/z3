; Choice term: choosing a function
; Second-order choice: choosing from function space
(set-logic HO_ALL)
(declare-fun Good () (-> (-> Int Int) Bool))
(assert (Good (lambda ((x Int)) (+ x 1))))
(define-fun chosen_f () (-> Int Int)
  (choice ((f (-> Int Int))) (Good f)))
(assert (not (Good chosen_f)))
(check-sat)
(exit)
