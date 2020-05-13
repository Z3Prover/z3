
; Copyright (c) 2015 Microsoft Corporation


(declare-fun f (Int) Int)

(assert (forall ((x Int) (y Int))
                (! (= (* x (f y)) (f (* x y)))
                   :pattern (* x (f y)))))

(assert (forall ((x Int) (y Int) (z Int))
                (! (= (* x (f y) (f z)) (f (* x y z)))
                   :pattern (* z (f y) (f x)))))

(check-sat)
