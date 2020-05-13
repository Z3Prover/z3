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
                 (fp #b0 #b10000110011 #b0100000000000000000000000000000000000000000000000000) ;; +0X1.4000000000000P+52 
                 (fp #b0 #b01111001011 #b1000000000000000000000000000000000000000000000000000)))) ;; +0X1.8000000000000P-52 

(assert (not (= q (fp #b0 #b01111001010 #b0000000000000000000000000000000000000000000000000000)))) ;; +0X1.0000000000000P-53 

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
