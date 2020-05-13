
; Copyright (c) 2015 Microsoft Corporation


(define-sort A () (Array Int Int Int))
(declare-fun foo (Int Int) Int)
(assert (forall ((x Int) (y Int)) (= (foo x y) (+ x y))))
(define-fun bag-union ((x A) (y A)) A
  ((_ map foo) x y))
(declare-const s1 A)
(declare-const s2 A)
(declare-const s3 A)
(assert (= s3 (bag-union s1 s2)))
(assert (= (select s1 0 0) 5))
(assert (= (select s2 0 0) 3))
(assert (= (select s3 0 0) 7))
(check-sat)

(reset)
(set-option :auto-config true)
(define-sort A () (Array Int Int Int))
(declare-fun foo (Int Int) Int)
(assert (forall ((x Int) (y Int)) (= (foo x y) (+ x y))))
(define-fun bag-union ((x A) (y A)) A
  ((_ map foo) x y))
(declare-const s1 A)
(declare-const s2 A)
(declare-const s3 A)
(assert (= s3 (bag-union s1 s2)))
(assert (= (select s1 0 0) 5))
(assert (= (select s2 0 0) 3))
(assert (= (select s3 0 0) 7))
(check-sat)

