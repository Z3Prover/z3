; Church numerals: zero and successor
(set-logic HO_ALL)
; Church numeral: n is represented as \f.\x. f^n(x)
(define-fun zero ((f (-> Int Int)) (x Int)) Int x)
(define-fun succ ((n (-> (-> Int Int) Int Int)) (f (-> Int Int)) (x Int)) Int
  (f (n f x)))
(define-fun one ((f (-> Int Int)) (x Int)) Int (succ zero f x))
(define-fun two ((f (-> Int Int)) (x Int)) Int (succ one f x))
(declare-fun inc () (-> Int Int))
(assert (= inc (lambda ((x Int)) (+ x 1))))
(assert (not (= (two inc 0) 2)))
(check-sat)
(exit)
