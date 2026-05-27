; Advanced: monad laws (Maybe monad)
(set-logic HO_ALL)
(declare-datatype (Maybe 1) ((par (T) ((nothing) (just (fromJust T))))))
(define-fun return_m ((x Int)) (Maybe Int) (just x))
(define-fun bind_m ((m (Maybe Int)) (f (-> Int (Maybe Int)))) (Maybe Int)
  (match m
    ((nothing (as nothing (Maybe Int)))
     ((just v) (f v)))))
; Left identity: bind (return a) f = f a
(declare-fun f () (-> Int (Maybe Int)))
(declare-fun a () Int)
(assert (not (= (bind_m (return_m a) f) (f a))))
(check-sat)
(exit)
