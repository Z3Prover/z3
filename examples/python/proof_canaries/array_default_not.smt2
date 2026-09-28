; Minimized from z3test t8.smt2. The array default axiom for (_ map not) over a
; Bool array introduces the term (not (default s)) as its own literal. Before the
; fix for negated Boolean terms in the proof checker, replaying the log rejected
; the tseitin and euf steps around it (unit (not (default s)) is not rup).
; Expected class for the clause-log cells once fixed: unverified-fallback (the
; array hints still fall back; there is no array plugin yet).
(declare-const s (Array Int Bool))
(assert (not (= (default ((_ map not) s)) (not (default s)))))
(check-sat)
