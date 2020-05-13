
; Copyright (c) 2015 Microsoft Corporation

(set-option :pp.max-depth 100)

(declare-fun f (Int Int) Int)
(declare-fun p (Int) Bool)
(declare-fun g (Int) Int)

(simplify (forall ((x Int) (y Int))
                  (forall ((w Int) (z Int))
                          (= (f x y) (f x z)))))

(simplify (forall ((x Int) (y Int))
                  (exists ((w Int) (z Int))
                          (= (f x y) (f x z)))))

(simplify (forall ((x Int))
                  (! (= (g x) (f x x))
                     :pattern ((g x))
                     :pattern ((g x))
                     :pattern ((f x x)))))

(simplify (forall ((x Int))
                  (forall ((y Int))
                          (! (= (f x y) 0)
                             :pattern ((f x y))))))

(simplify (exists ((x Int))
                  (exists ((y Int))
                          (= (f x y) 0))))

                          

