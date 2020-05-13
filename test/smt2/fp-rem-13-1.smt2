;; Copyright (c) 2016 Microsoft Corporation

(set-logic QF_FP)
(set-info :source |Handcrafted by C.M. Wintersteiger from a bug repro by Florian Schanda; GitHub Issue #508|)
(set-info :smt-lib-version 2.5)
(set-info :category crafted)
(set-info :status unsat)

(declare-fun x () Float64)
(declare-fun y () Float64)
(declare-fun r () Float64)

(assert (= x (fp #b0 #b11111111110 #b0000000000000000000000000000000000000000000000000000))) ;; +0X1.0000000000000P+1023 
(assert (= r (fp.rem x y)))

(assert (= y (fp #b0 #b11110111110 #b0100000000000000000000000000000000000000000000000000))) ;; +0X1.4000000000000P+959, D=64
(assert (not (= r (fp #b1 #b11110111100 #b0000000000000000000000000000000000000000000000000000)))) ;; -0X1.0000000000000P+957
(check-sat)
(exit)
