; Under not r, neither choice of p can satisfy all four background clauses.
; The native refutation contains local hypothesis and lemma nodes.
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (or p q))
(assert (or (not p) q r))
(assert (or p (not q) r))
(assert (or (not p) (not q) r))
(assert (not r))
