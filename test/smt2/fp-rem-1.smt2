;; Copyright (c) 2016 Microsoft Corporation

(set-logic QF_FP)
(set-info :source |Handcrafted by Christoph M. Wintersteiger (cwinter@microsoft.com).|)
(set-info :status sat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)

(assert (= x (fp.rem (_ +zero 11 53) (fp #b0 #b01111111111 #x0000000000000))))

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(get-model)
(exit)
