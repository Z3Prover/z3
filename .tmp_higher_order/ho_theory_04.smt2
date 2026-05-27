; HO + Bitvectors: lambda over bitvectors
(set-logic HO_ALL)
(define-fun bv_inc () (-> (_ BitVec 8) (_ BitVec 8))
  (lambda ((x (_ BitVec 8))) (bvadd x #x01)))
(assert (not (= (bv_inc #xFF) #x00)))
(check-sat)
(exit)
