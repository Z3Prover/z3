;; Copyright (c) 2016 Microsoft Corporation

(set-logic QF_FP)
(set-info :status sat)
(set-info :source "Handcrafted by CM Wintersteiger")
    
(define-sort FPN () (_ FloatingPoint 5 11))
(declare-const x FPN)
(declare-const y FPN)
(declare-const r FPN)

(assert (= x (fp #b0 #b10001 #b1100000000))) ;; +7.0
(assert (= y (fp #b0 #b10001 #b0000000000))) ;; +4.0
(assert (= r (fp.rem x y)))
                 
(check-sat)
(get-value (r))
(check-sat-using smt)
(get-value (r))
(check-sat-using (then fpa2bv smt))
(get-value (r))
(check-sat-using (then fpa2bv smt))
(get-value (r))
(exit)
