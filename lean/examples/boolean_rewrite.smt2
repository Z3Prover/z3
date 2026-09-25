; The native refutation uses implication rewrites and modus ponens.
(set-option :produce-proofs true)
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(assert (=> p q))
(assert (not q))
(check-sat)
(get-proof)
