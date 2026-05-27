; HO + Reals: approximation via HO function
(set-logic HO_ALL)
(declare-fun approx () (-> (-> Real Real) Real Real Real))
; approx f a = f(a) is trivial approximation
(assert (forall ((f (-> Real Real)) (a Real))
  (= (approx f a) (f a))))
(declare-fun myf () (-> Real Real))
(assert (= myf (lambda ((x Real)) (* x x))))
(assert (not (= (approx myf 3.0) 9.0)))
(check-sat)
(exit)
