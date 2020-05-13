;; Copyright (c) 2016 Microsoft Corporation

(set-logic QF_FP)
(set-info :source |Handcrafted by C.M. Wintersteiger from a bug repro by Florian Schanda; GitHub Issue #508|)
(set-info :smt-lib-version 2.5)
(set-info :category crafted)
(set-info :status unsat)

(declare-fun a () Float16)
(declare-fun b () Float16)
(declare-fun r () Float16)
(declare-fun s () Float16)

(assert (= a (fp #b1 #b00000 #b1110111111)))
(assert (= b (fp #b0 #b00000 #b0000001110)))

(assert (= r (fp.rem a b)))

(assert (= s (fp.rem
                 (fp #b1 #b00000 #b1110111111)
                 (fp #b0 #b00000 #b0000001110))))

(assert (not (= r s)))

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
