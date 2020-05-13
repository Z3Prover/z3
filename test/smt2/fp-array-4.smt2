;; Copyright (c) 2015 Microsoft Corporation

(set-info :status sat)
(set-info :source |Handcrafted by Christoph M. Wintersteiger (cwinter@microsoft.com).|)

(declare-const x Int)
(declare-const y Int)
(declare-fun A () (Array Int (_ FloatingPoint 53 11)))

(assert (fp.lt (select A x) (select A y)))

(check-sat)
(exit)
