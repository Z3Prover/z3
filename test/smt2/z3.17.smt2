
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

; declare a mutually recursive parametric datatype
(declare-datatypes (T) ((Tree leaf (node (value T) (children TreeList)))
                        (TreeList nil (cons (car Tree) (cdr TreeList)))))
(declare-const t1 (Tree Int))
(declare-const t2 (Tree Bool))
; we must use the 'as' construct to distinguish the leaf (Tree Int) from leaf (Tree Bool)
(assert (not (= t1 (as leaf (Tree Int)))))
(assert (> (value t1) 20))
;(assert (not ((_ is ((Tree Bool)) Bool leaf ) t2)))
(assert (not (value t2)))
(check-sat)
(get-model)
