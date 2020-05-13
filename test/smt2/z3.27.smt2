
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

(simplify (bvor #x6 #x3))   ; bitwise or
(simplify (bvand #x6 #x3))  ; bitwise and
(simplify (bvnot #x6)) ; bitwise not
(simplify (bvnand #x6 #x3)) ; bitwise nand
(simplify (bvnor #x6 #x3)) ; bitwise nor
(simplify (bvxnor #x6 #x3)) ; bitwise xnor


