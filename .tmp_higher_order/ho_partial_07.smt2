; Partial application: const function
(set-logic HO_ALL)
(define-fun const_fn ((c Int)) (-> Int Int)
  (lambda ((x Int)) c))
(declare-fun always7 () (-> Int Int))
(assert (= always7 (const_fn 7)))
(assert (not (= (always7 999) 7)))
(check-sat)
(exit)
