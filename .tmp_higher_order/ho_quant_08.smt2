; HO quantification: function space cardinality
; No injective function from 3-element type to 2-element type
(set-logic HO_ALL)
(declare-datatype Three ((A) (B) (C)))
(declare-datatype Two ((X) (Y)))
(assert (exists ((f (-> Three Two)))
  (forall ((a Three) (b Three)) (=> (= (f a) (f b)) (= a b)))))
(check-sat)
(exit)
