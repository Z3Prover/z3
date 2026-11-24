; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_7_overlapping_cycles.smt2
(set-logic ALL)
(declare-fun x () String)

;; R = ((ab) | (aba))*
;; This regex is heavily non-left-unitary, as discussed in the paper.
;; The prefix combinations of "ab" and "aba" heavily overlap and mask each other.
(define-fun ab () (RegEx String) (str.to_re "ab"))
(define-fun aba () (RegEx String) (str.to_re "aba"))
(define-fun R () (RegEx String) (re.* (re.union ab aba)))

;; Checking if heavily branching, overlapping cycles can be fused correctly by the SCC algorithm.
;; A naive unwinder branches exponentially here because `ab` vs `aba` repeatedly fractures the trace space.
;; With the SCC tracking natively merging nodes (merging states that return to the cycle root), the derivation graph should gracefully stabilize to an underapproximating projection.
(assert (str.in_re (str.++ "a" x "b" x "a" x) R))
(check-sat)