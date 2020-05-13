; Copyright (c) 2018 Microsoft Corporation
; GitHub issue

(set-option :produce-models true)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-const c (Array Int Int))
(declare-const lena Int)
(declare-const lenb Int)
(declare-const lenc Int)
(assert (<= 0 lena))
(assert (<= 0 lenb))
(assert (< 0 lenc))
(assert (= lenc (+ lena lenb)))
(assert (= 65 (select c 0)))
(assert (forall ((x Int))
                (!
                (=> (and (> x 0) (<= x lenb))
                (= (select c x) (select b x)))
                :pattern ((select c x)) 
                :pattern ((select b x)))))
(assert (forall ((x Int))
                (!
                (=> (and (>= x 0) (< x lenb))
                (= (select c x) (select b x)))
                :pattern ((select c x)) 
                :pattern ((select b x)))))
(assert (forall ((x Int))
                (!
                (=> (and (>= x lenb) (< x (+ lena lenb)))
                (= (select c x) (select a (- x lenb))))
                :pattern ((select c x)))))
(check-sat)
