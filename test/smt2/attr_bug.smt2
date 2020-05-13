
; Copyright (c) 2015 Microsoft Corporation

(declare-fun f (Int) Bool)

(display (forall ((x Int)) (! (f x) :skolemid |foo:10|)))