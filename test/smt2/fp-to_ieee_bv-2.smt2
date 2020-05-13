(set-logic QF_BVFP)

(set-option :rewriter.hi_div0 false)
(set-option :rewriter.hi_fp_unspecified false)
(set-option :model_validate true)

(declare-const x (_ FloatingPoint 8 24))
;(declare-const y (_ FloatingPoint 8 24))
(declare-const b (_ BitVec 32))

(assert (= b (to_ieee_bv x)))
(assert (fp.isNaN x))
(assert (= b #xff800003))

(check-sat)
(get-model)
(get-value (b))
(eval (to_ieee_bv (_ NaN 8 24)))
(eval (bvudiv b (_ bv0 32)))
(simplify (to_ieee_bv (_ NaN 8 24)))
(simplify (bvudiv b (_ bv0 32)))

(check-sat-using (then fpa2bv smt))
;(get-model)

(exit)
