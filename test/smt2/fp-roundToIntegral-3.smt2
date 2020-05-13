; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FP)
;;(set-info :status unsat)
(set-info :source "Handcrafted by CM Wintersteiger")

(define-sort FPN () (_ FloatingPoint 5 11))

(declare-fun x () FPN)
(assert (= x (fp #b0 #b01111 #b1100000000))) ;; 1.75

(declare-fun r () FPN)
(assert (= r (fp.roundToIntegral roundNearestTiesToEven x)))

(assert (not (= r (fp #b0 #b10000 #b0000000000))))

(check-sat)
(check-sat-using smt)
(check-sat-using (then
                     fpa2bv
                     (using-params simplify :elim_and true)
                     bit-blast
                     sat))
(exit)
