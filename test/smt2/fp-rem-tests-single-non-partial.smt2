;; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FP)
(set-info :source "Handcrafted by CM Wintersteiger")
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 8 24))
(declare-const x FPN)
(declare-const y FPN)
(declare-const r FPN)

(push)
(assert (= x (fp #b0 #b00000000 #b01000000000000000000000)))
(assert (= y (fp #b0 #b00000000 #b11000000000000000000000)))
(assert (= r (fp.rem x y)))
(assert (not (= r (fp #b0 #b00000000 #b01000000000000000000000))))
(check-sat-using qffp)
;;(check-sat-using (then fpa2bv smt))
(pop)

(exit)
