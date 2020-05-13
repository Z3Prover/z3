
; Copyright (c) 2015 Microsoft Corporation
(set-option :parser.ignore-bad-patterns false)

(declare-fun f (Int Int) Int)
(declare-fun a () Int)

(display (forall ((x Int) (y Int))
                 (! (= (f x y) x)
                    :pattern ((f x y)))))

(display (forall ((x Int) (y Int))
                 (! (= (f x y) x)
                    :pattern (f x y))))

(display (forall ((x Int) (y Int))
                 (! (= (f x y) x)
                    :pattern ((f x y) (f y x)))))

(display (forall ((x Int) (y Int))
                 (! (= (f x y) x)
                    :pattern x)))

(display (forall ((x Int) (y Int))
                 (! (= (f x y) x)
                    :pattern a)))

