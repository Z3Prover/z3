
; Copyright (c) 2015 Microsoft Corporation


(declare-const b Bool)

(simplify
 (bvadd #x10
        (ite b #x40 #x00))
 :pull-cheap-ite true)


(simplify
 (bvadd (ite b #x40 #x00)
        #x20)
 :pull-cheap-ite true)


(simplify
 (bvudiv (ite b #x08 #x04)
         #x02)
 :pull-cheap-ite true)

(simplify
 (bvudiv #xf0 (ite b #x08 #x04))
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
 (bvadd #x10
        (ite b x #x00))
 :pull-cheap-ite true)

(simplify
 (bvadd #x10
        (ite b #x00 x))
 :pull-cheap-ite true)


(simplify
 (bvadd (ite b x #x00)
        #x20)
 :pull-cheap-ite true)

(simplify
 (bvadd (ite b #x00 x)
        #x20)
 :pull-cheap-ite true)


