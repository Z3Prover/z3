; Verification: abstraction refinement
(set-logic HO_ALL)
(declare-fun alpha () (-> Int Int))  ; abstraction function
(declare-fun gamma () (-> Int Int))  ; concretization
; Galois connection: alpha . gamma . alpha = alpha
(assert (forall ((x Int)) (= (alpha (gamma (alpha x))) (alpha x))))
(declare-fun concrete_op () (-> Int Int))
(declare-fun abstract_op () (-> Int Int))
; soundness: alpha(concrete_op(x)) <= abstract_op(alpha(x))
(assert (forall ((x Int)) (<= (alpha (concrete_op x)) (abstract_op (alpha x)))))
(assert (= (alpha 5) 1))
(assert (= (concrete_op 5) 7))
(assert (not (<= (alpha 7) (abstract_op 1))))
(check-sat)
(exit)
