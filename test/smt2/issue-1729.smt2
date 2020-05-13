; GitHub issue

(assert (forall ((x (_ BitVec 4)))
                (forall ((y (_ BitVec 4)))
                        (= (bvadd x y) #x0))))

(apply (using-params bit-blast :blast-quant true))
