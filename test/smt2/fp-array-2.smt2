;; Copyright (c) 2015 Microsoft Corporation

(set-info :status sat)
(set-info :source |Handcrafted by Christoph M. Wintersteiger (cwinter@microsoft.com).|)

(declare-fun A () (Array Int (_ FloatingPoint 11 53)))

(assert (fp.eq (select A 0) (select A 1)))

(check-sat)
(exit)
