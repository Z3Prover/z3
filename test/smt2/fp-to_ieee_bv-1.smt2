
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FPBV)
(set-info :status sat)
(set-option :produce-models true)

; floats
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(declare-const r (_ FloatingPoint 11 53))

; bit-vectors
(declare-const x_bv (_ BitVec 64))
(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))

(assert 
 (and 
  ; r = x + y
  (= x ((_ to_fp 11 53) roundTowardZero 0.5 0))
  (= y ((_ to_fp 11 53) roundTowardZero 0.5 0))
  (= r (fp.add roundTowardZero x y))

  ; x_bv = x converted to an ieee-compliant bit-vector
  (= x_bv (to_ieee_bv x))

  ; a = b xor x_bv
  (= a (bvxor b x_bv))
  )
 )

(check-sat)
(check-sat-using smt)
(exit)
