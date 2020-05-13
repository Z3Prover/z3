
; Copyright (c) 2015 Microsoft Corporation

(set-option :produce-models true)
(declare-const s1 (Array Int Int))
(declare-const s2 (Array Int Int))
(declare-const a Int)
(declare-const b Int)
(assert (select ((_ map (<= (Int Int) Bool)) s1 s2) a))
(assert (not (select ((_ map (<= (Int Int) Bool)) s1 s2) b)))
(check-sat)
(eval (<= (select s1 a) (select s2 a)))
(eval (<= (select s1 b) (select s2 b)))

