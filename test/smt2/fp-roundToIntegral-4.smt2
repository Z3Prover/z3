; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FP)
(set-info :source "Handcrafted by CM Wintersteiger")

(define-sort FPN () (_ FloatingPoint 5 11))

(declare-fun x () FPN)
(assert (= x (fp #b1 #b10000 #b1100000000)))

(declare-fun r () FPN)
(declare-fun m () FPN)
(assert (= r (fp.roundToIntegral roundNearestTiesToEven x)))
(assert (= m (fp.roundToIntegral roundNearestTiesToEven (fp #b1 #b10000 #b1100000000))))

(check-sat)
(get-value (x))
(get-value (r))
(get-value (m))

(check-sat-using smt)
(get-value (r))

(check-sat-using (then
                     fpa2bv
                     (using-params simplify :elim_and true)
                     bit-blast
                     sat))

(get-value (r))
(exit)
