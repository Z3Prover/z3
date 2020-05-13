
; Copyright (c) 2015 Microsoft Corporation


(declare-const b Bool)
(declare-const c1 Bool)
(declare-const c2 Bool)

(simplify
 (bvadd #x10
        (ite b #x40 (ite c1 #x00 #x01)))
 :pull-cheap-ite true)


(simplify
 (bvadd (ite b (ite c1 #x40 #x20) (ite c2 #x00 #x10))
        #x20)
 :pull-cheap-ite true)


(simplify
 (bvadd (ite b #x08 (ite c1 #x04 #x60))
         #x02)
 :pull-cheap-ite true)

(simplify
 (bvadd #xf0 (ite b #x08 (ite c1 (ite c2 #x01 #x02) #x04)))
 :pull-cheap-ite true)


(simplify
 (= 5 (ite b 2 3))
 :pull-cheap-ite true)

(simplify
 (= (ite b 2 3) 5)
 :pull-cheap-ite true)

(simplify
 (= (ite b 5 3) 5)
 :pull-cheap-ite true)

(declare-const x (_ BitVec 8))

(simplify
 (bvadd #xf0 (ite b #x08 (ite c1 (ite c2 x #x02) #x04)))
 :pull-cheap-ite true)


(simplify
 (bvadd #xf0 (ite b #x08 (ite c1 (ite c2 #x01 #x02) x)))
 :pull-cheap-ite true)

