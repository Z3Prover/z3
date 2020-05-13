;; Copyright (c) 2015 Microsoft Corporation

(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun c1 () (_ BitVec 1))
(declare-fun c2 () (_ BitVec 8))
(declare-fun c3 () (_ BitVec 23))

;; fp-conversions-10.smt2...
(assert (= (fp.to_real (_ NaN 8 24)) (fp.to_real (fp c1 c2 c3))))

;; but make it all linear...
(assert (= c2 #xFF)) 

(check-sat)
(check-sat-using smt)
(exit)

