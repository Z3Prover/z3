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
                 (fp #b0 #b01111111111 #xF0F0F0F0F0F0F) ;; +0X1.F0F0F0F0F0F0FP+0 
                 (fp #b0 #b01111111111 #x0F0F0F0F0F0F0)))) ;; +0X1.0F0F0F0F0F0F0P+0 

(assert (not (= q (fp #b1 #b01111111100 #b0110100101101001011010010110100101101001011010001000)))) ;; -0X1.6969696969688P-3 

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
