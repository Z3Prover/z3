; The native refutation also uses trans, monotonicity, and not-or-elim.
(set-option :produce-proofs true)
(declare-const p Bool)
(declare-const q Bool)
(assert (not (or (not p) q)))
(assert (not (and p (not q))))
(check-sat)
(get-proof)
