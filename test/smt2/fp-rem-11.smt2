;; Copyright (c) 2016 Microsoft Corporation

(set-logic QF_FP)
(set-info :source |Handcrafted by C.M. Wintersteiger from a bug repro by Florian Schanda; GitHub Issue #508|)
(set-info :smt-lib-version 2.5)
(set-info :category crafted)
(set-info :status unsat)

(define-fun a () Float16 (fp #b1 #b00000 #b0000000011))
(define-fun l () Float16 (fp #b1 #b00000 #b0000000001))

(declare-fun b () Float16)
(declare-fun r () Float16)
(declare-fun s () Float16)

(assert (= l (fp.neg b)))

(assert (= r (fp.rem a b))) ;; blasted via fpa2bv
(assert (= s (fp.rem a (fp.neg l)))) ;; simplified on mpf's.

(assert (not (= r s)))

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
