; The native refutation uses asserted, rewrite, mp, and unit-resolution.
(set-option :produce-proofs true)
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(assert (=> p q))
(assert (not q))
(check-sat)
(get-proof)
