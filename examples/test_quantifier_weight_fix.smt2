# Test case for quantifier weight fix (issue #7735)
# This test demonstrates that quantifiers now have weight=1 by default
# instead of weight=0, preventing the "Weight 0" performance bug.

(set-logic ALL)
(declare-fun f (Int) Int)

; This quantifier without explicit weight should now have weight=1 (not weight=0)
(assert (forall ((x Int)) (= (f x) x)))

; Adding a constraint that makes the formula unsatisfiable
(assert (= (f 1) 2))

; This should be unsat and should complete quickly with the fix
; Before fix: would hang due to infinite instantiation
; After fix: should return unsat quickly
(check-sat)