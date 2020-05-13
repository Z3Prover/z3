
; Copyright (c) 2015 Microsoft Corporation


(declare-fun f (Int Int) Int)

(set-option :pp.max-depth 10)

(display (forall ((x Int) (y0 Int))
                 (let ((y (f x y0)))
                   (or (forall ((z Int))
                            (or (= (f z x) (f y x))
                                       (exists ((w Int))
                                               (= (f z w) (f y x)))))
                       (> (f y y) 0)))))
        