; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger; github issue #331.")

(declare-fun da () (_ FloatingPoint 11 53))
(declare-fun fa () (_ FloatingPoint 8 24))

(define-fun done () (_ FloatingPoint 11 53) (fp #b0 #b01111111111 #x0000000000000))
(define-fun fone () (_ FloatingPoint 8 24) (fp #b0 #x7f #b00000000000000000000000))

(assert (fp.gt da done))
(assert (= fa ((_ to_fp 8 24) RTP da)))
(assert (fp.leq fa ((_ to_fp 8 24) RNE 1.0)))

(check-sat)
