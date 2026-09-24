; A native Boolean gate clause connects XOR rewriting to unit resolution.
(set-option :produce-proofs true)
(declare-const p Bool)
(declare-const q Bool)
(assert (xor p q))
(assert p)
(assert q)
(check-sat)
(get-proof)
