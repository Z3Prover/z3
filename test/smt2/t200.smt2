
; Copyright (c) 2015 Microsoft Corporation
(set-logic AUFLIA)
(set-option :smt.mbqi true)
(set-option :smt.mbqi.max-iterations 10)
(set-option :print-warning false)
(declare-sort PZ 0)
(declare-fun MS (Int PZ) Bool)
(declare-fun X0 (Int) PZ)
(declare-fun a () Int)
(assert (forall ((x Int))
                (exists ((X PZ))
                        (and (MS x X) 
                             (forall ((y Int))
                                     (=> (MS y X) (= y x)))))))

(check-sat)