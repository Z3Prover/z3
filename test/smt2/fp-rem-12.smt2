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
                 (fp #b0 #b10000000100 #x8000000000001) ;; 48.0
                 (fp #b0 #b01111111111 #x0800000000001) ;; 1.03125 ;; (fp.rem x y) should be -0.46875
                 )))               

(assert (not (= q (fp #b1 #b01111111101 #xE00000000003C)))) ;; want -0X1.E00000000003CP-2


(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
