(assert (forall ((a Bool) (b Bool) (d (_ BitVec 1)) (e (_ BitVec 1)) (f (_ BitVec 1)) (g Bool))
     (= (= f (ite a (_ bv0 1) (ite (not (= d (_ bv0 1))) (_ bv0 1) (ite b e e)))) g)))
(check-sat-using horn)