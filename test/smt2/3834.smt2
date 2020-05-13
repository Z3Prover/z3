(set-logic HORN)
(set-option :fp.xform.bit_blast true)
(assert (forall ((q59 (_ BitVec 10)) (q60 (_ BitVec 10)) (q61 (_ BitVec 10)) (q62 (_ BitVec 16))) (distinct (bvnand q60 (_ bv0 10)) (bvlshr q59 q60))))
(check-sat)