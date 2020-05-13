;; Copyright (c) 2015 Microsoft Corporation

(set-info :source |Handcrafted by Christoph M. Wintersteiger (cwinter@microsoft.com).|)
(set-info :status sat)
(set-option :model_validate true)
(set-option :smt.relevancy 2)
(set-option :rewriter.hi_fp_unspecified false)

(declare-fun A () (Array (_ FloatingPoint 8 24) (_ FloatingPoint 11 53)))
(declare-fun A2 () (Array (_ FloatingPoint 8 24) (_ FloatingPoint 11 53)))

(assert (not (= A A2)))

(assert (=
            (select A (_ +oo 8 24))
            (select A (_ -oo 8 24))))

(assert (not (= (select A (_ +oo 8 24)) (_ NaN 11 53))))
(assert (not (= (select A (_ +oo 8 24)) (_ +zero 11 53))))

(declare-fun B () (Array Int (_ FloatingPoint 11 53)))
(assert (not (= (select B 0) (select B 1))))

(declare-fun C () (Array (_ FloatingPoint 11 53) Int))
(assert (not (= (select C (_ +oo 11 53)) 2)))
(assert (not (= (select C (_ -oo 11 53)) 2)))

(declare-fun D () (Array Int (Array Int (_ FloatingPoint 11 53))))
(assert (not (= (select (select D 1) 2) (_ -oo 11 53))))
(assert (not (= (select (select D 2) 3) (_ +oo 11 53))))

(declare-fun AP () (_ FloatingPoint 11 53))
(assert (= AP (select A (_ +oo 8 24))))

(check-sat-using smt)
;(get-value (AP))
(get-value (C))

(exit)
