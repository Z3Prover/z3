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
                 (fp #b0 #b10000011001 #x0800000000000)    ;; +0X1.0800000000000P+26 
                 (fp #b0 #b01111100101 #x0A00000000000)))) ;; +0X1.0A00000000000P-26 

(assert (not (= q (fp #b0 #b01111100011 #b0000100000000000000000000000000000000000000000000000)))) ;; +0X1.0800000000000P-28 

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
