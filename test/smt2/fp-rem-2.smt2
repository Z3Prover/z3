;; Copyright (c) 2016 Microsoft Corporation

(set-logic QF_FP)
(set-info :source |Handcrafted by C.M. Wintersteiger from a bug repro by Florian Schanda; GitHub Issue #508|)
(set-info :smt-lib-version 2.5)
(set-info :category crafted)
(set-info :status unsat)

(define-fun x () Float16 (fp #b1 #b00000 #b1110111111)) ;; ((_ to_fp 5 11) RTZ -0.9365234375 -14 [- 959 -15 D])
(define-fun l () Float16 (fp #b1 #b00000 #b0000001110)) 

(declare-fun y () Float16)
(declare-fun r () Float16)
(declare-fun s () Float16)

(assert (= l (fp.neg y)))
(assert (= r (fp.rem x y)))
(assert (not (= r (fp #b1 #b00000 #b0000000111)))) ;; ((_ to_fp 5 11) RTZ -0.0068359375 -14 [- 7 -15 D])

(check-sat)
(check-sat-using smt)
(check-sat-using (then fpa2bv smt))
(exit)
