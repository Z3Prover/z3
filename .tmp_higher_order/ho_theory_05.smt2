; HO + Bitvectors: higher-order quantification over BV functions
(set-logic HO_ALL)
(assert (exists ((f (-> (_ BitVec 4) (_ BitVec 4))))
  (forall ((x (_ BitVec 4))) (= (f (f x)) x))))
(check-sat)
(exit)
