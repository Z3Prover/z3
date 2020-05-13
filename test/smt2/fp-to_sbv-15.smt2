
; Copyright (c) 2015 Microsoft Corporation
(set-info :source "Handcrafted by C.M. Wintersteiger")
(set-info :status unsat)

(define-fun X () (_ FloatingPoint  8 24) ((_ to_fp 8 24) RNE (/ 244681 4194304)))
(declare-fun R () (_ BitVec 8))

(assert (and
			(= R ((_ fp.to_sbv 8) RNE X))			
			(not (= R #x00))
		))

(check-sat)
(check-sat-using smt)
(exit)
