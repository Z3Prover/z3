
; Copyright (c) 2015 Microsoft Corporation
(set-option :smt.macro-finder true)
(set-option :auto-config true)

(declare-fun f ((_ BitVec 1)) (_ BitVec 1))
(declare-fun P ((_ BitVec 1)) Bool)
(declare-fun Q ((_ BitVec 1)) Bool)
(declare-const a (_ BitVec 1))

(assert (forall ((x (_ BitVec 1))) (= (= (f x) a) (or (P x) (Q x)))))

(check-sat)
