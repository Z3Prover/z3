
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

(echo "starting Z3...")
(declare-const a Int)
(declare-fun f (Int Bool) Int)
