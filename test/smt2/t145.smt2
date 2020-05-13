
; Copyright (c) 2015 Microsoft Corporation
(declare-const v0 (_ BitVec 8))
(simplify (bvashr (bvashr v0 #x01) v0))
(declare-const v1 (_ BitVec 8))
(simplify (bvashr (bvashr v0 v1) #x01))