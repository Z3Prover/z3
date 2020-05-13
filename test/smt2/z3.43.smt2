
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

(set-option :smt.mbqi true)
(set-option :model.compact true)

;; T is an uninterpreted sort
(declare-sort T) 

(declare-fun subtype (T T) Bool)

;; subtype is reflexive
(assert (forall ((x T)) (subtype x x)))

;; subtype is antisymmetric
(assert (forall ((x T) (y T)) (=> (and (subtype x y)
                                       (subtype y x))
                                       (= x y))))
;; subtype is transitive
(assert (forall ((x T) (y T) (z T)) (=> (and (subtype x y)
                                             (subtype y z))
                                             (subtype x z))))
;; subtype has the tree-property
(assert (forall ((x T) (y T) (z T)) (=> (and (subtype x z)
                                             (subtype y z))
                                        (or (subtype x y)
                                            (subtype y x)))))

;; now we define a simple example using the axiomatization above.
(declare-const obj-type T)
(declare-const int-type T)
(declare-const real-type T)
(declare-const complex-type T)
(declare-const string-type T)

;; we have an additional axiom: every type is a subtype of obj-type
(assert (forall ((x T)) (subtype x obj-type)))

(assert (subtype int-type real-type))
(assert (subtype real-type complex-type))
(assert (not (subtype string-type real-type)))
(declare-const root-type T)
(assert (subtype obj-type root-type))
(check-sat)
;; (get-model)

(echo "Is int-type a subtype of complex-type?")
(eval (subtype int-type complex-type))
(echo "Is int-type = obj-type?")
(eval (= int-type obj-type))
(echo "Is int-type a subtype of root-type?")
(eval (subtype int-type root-type))
(echo "Is root-type = obj-type?")
(eval (= root-type obj-type))
