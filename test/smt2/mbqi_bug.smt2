
; Copyright (c) 2015 Microsoft Corporation
; We Enconde each set S of integers as a function S : Int -> Bool
(declare-fun S1 (Int) Bool)
; To assert that A and C are elements of S1, we just assert (S1 A) and (S1 C) 
(declare-const A Int)
(declare-const C Int)
(assert (S1 A))
(assert (S1 C))
; To say that B is not an element of S1, we just assert (not (S1 B))
(declare-const B Int)
(assert (not (S1 B)))

; Now, let max_S1 be the max value in S1
(declare-const max_S1 Int)
; Then, we now that max_S1 is an element of S1, that is
(assert (S1 max_S1))
; All elements in S1 are smaller than or equal to max_S1
; (assert (forall ((x Int)) (or (not (S1 x)) (not (>= x (+ max_S1 1))))))
(assert (forall ((x Int)) (=> (S1 x) (<= x max_S1))))

; Now, let us define a set S2 and S3
(declare-fun S2 (Int) Bool)
(declare-fun S3 (Int) Bool)
; To assert that S3 is equal to the union of S1 and S2, we just assert
(assert (forall ((x Int)) (= (S3 x) (or (S1 x) (S2 x)))))

; To assert that S3 is not equal to S1 we assert
(assert (exists ((x Int)) (not (= (S3 x) (S1 x)))))

(check-sat)
