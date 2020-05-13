
; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FPBV)
(set-info :status sat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () (_ BitVec 32))
(declare-fun r () FPN)
(declare-fun q () FPN)

(assert (= x #x00000003))
(assert (= r (fp #b0 #b10000000000 #b1000000000000000000000000000000000000000000000000000)))
(assert (= q ((_ to_fp_unsigned 11 53) RTZ x)))

;; (assert (fp.eq r q))
;; (assert (= r q))
;; (assert (= ((_ fp.to_ubv 8) RNE r) ((_ fp.to_ubv 8) RNE q)))

(declare-fun qc () (_ BitVec 64))
(declare-fun rc () (_ BitVec 64))

(assert (= qc (to_ieee_bv q)))
(assert (= rc (to_ieee_bv r)))
(assert (= qc rc))

(check-sat)
(check-sat-using smt)
