
; Copyright (c) 2015 Microsoft Corporation

(set-option :produce-models true)
(check-sat)
(eval (bv2int (bvadd #x0a #xf0)))