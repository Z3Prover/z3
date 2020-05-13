;; Copyright (c) 2016 Microsoft Corporation

(set-logic QF_FP)
(set-info :source |Handcrafted by Christoph M. Wintersteiger (cwinter@microsoft.com).|)
(set-info :category "crafted")
(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun r () FPN)
(declare-fun q () FPN)
(declare-fun m () FPN)

(assert (= q (fp.rem
                 (fp #b0 #b11111111110 #xFFFFFFFFFFFFF)
                 (fp #b0 #b00000000001 #x0000000000000))))

(assert (not (= q (_ +zero 11 53))))

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
