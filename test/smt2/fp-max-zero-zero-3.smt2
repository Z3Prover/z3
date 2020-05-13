;; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FP)
(set-info :source |Handcrafted by C.M. Wintesteiger, inspired by github issue #616.|)
(set-info :status unsat)

(declare-fun X () (_ FloatingPoint 2 3))

(assert (not (fp.isZero X)))
(assert (= X (fp.max (_ -zero 2 3) (fp.max (_ +zero 2 3) (_ -zero 2 3)))))

(check-sat)
(check-sat-using (then simplify fpa2bv smt))
(check-sat-using (then simplify smt))
