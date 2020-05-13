
(assert (forall ((u (_ BitVec 4)))
			(and
				(exists ((e1 (_ BitVec 4)) (e2 (_ BitVec 6)) (e3 (_ BitVec 6)))
					(and
						(= u e1)
						(= e2 e3)))
				(exists ((e22 (_ BitVec 4)))					
						(= u e22)))))

(apply simplify)
(apply (then (using-params elim-small-bv :max_bits 4) simplify))

