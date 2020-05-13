
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

(simplify (bvule #x0a #xf0))  ; unsigned less or equal
(simplify (bvult #x0a #xf0))  ; unsigned less than
(simplify (bvuge #x0a #xf0))  ; unsigned greater or equal
(simplify (bvugt #x0a #xf0))  ; unsigned greater than
(simplify (bvsle #x0a #xf0))  ; signed less or equal
(simplify (bvslt #x0a #xf0))  ; signed less than
(simplify (bvsge #x0a #xf0))  ; signed greater or equal
(simplify (bvsgt #x0a #xf0))  ; signed greater than
