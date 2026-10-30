; The background entails r by cases on p or q.
; The last assertion is the designated negated goal, not an exported axiom.
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (or p q))
(assert (or (not p) r))
(assert (or (not q) r))
(assert (not r))
