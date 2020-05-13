
; Copyright (c) 2015 Microsoft Corporation


(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))

(simplify (= (bvsub a b) #x01))
(simplify (= (bvsub a b) #x00))
(simplify (= (bvadd (bvmul #xff a) b) #x01))
(simplify (= (bvadd (bvmul #xff a) b) #x00))
(simplify (= (bvadd (bvmul #xff a) (bvmul #xff b)) #x01))
(simplify (= (bvadd (bvmul #xff a) (bvmul #xff b)) #x00))
(simplify (= (bvadd (bvmul #xfa a) (bvmul #xff b)) #x01))
(simplify (= (bvadd (bvmul #xfa a) (bvmul #xff b)) #x00))
(simplify (= (bvadd (bvmul #xfa a) (bvmul #xfb b)) #x01))
(simplify (= (bvadd (bvmul #xfa a) (bvmul #xfb b)) #x00))
