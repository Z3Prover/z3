; Instantiate the non-Horn universal clause at a, then derive q(a).
(declare-sort U 0)
(declare-const a U)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(assert (forall ((x U)) (or (p x) (q x))))
(assert (not (p a)))
(assert (not (q a)))
