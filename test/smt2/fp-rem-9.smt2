;; Copyright (c) 2016 Microsoft Corporation

(set-logic QF_FP)
(set-info :source |Handcrafted by C.M. Wintersteiger from a bug repro by Florian Schanda; GitHub Issue #508|)
(set-info :smt-lib-version 2.5)
(set-info :category crafted)
(set-info :status unsat)

(define-fun a () Float32 (fp #b0 #b00000000 #b11000000000000000000000))
(define-fun b () Float32 (fp #b0 #b00000000 #b01000000000000000000000))

(declare-fun r () Float32)

(assert (= r (fp.rem a b)))
(assert (not (= r (_ +zero 8 24))))

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
