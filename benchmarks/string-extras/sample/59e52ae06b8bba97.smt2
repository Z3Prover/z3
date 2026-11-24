; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_15_multivar_subsume.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

;; Test: Cross-Variable Extended Subsumption (Section 4.2.4)
(define-fun bc () (RegEx String) (str.to_re "bc"))
(define-fun R () (RegEx String) (re.* bc))

;; Primitive bounds placing all three variables in the cycle natively:
(assert (str.in_re x R))
(assert (str.in_re y R))
(assert (str.in_re z R))

;; Deep substitution target constraint:
(assert (str.in_re (str.++ x y z "c" x y) R))

;; Why it is hard:
;; A naive solver unwinds `x`, then `y`, then `z` looking for the conflict.
;; A smart solver relying on the "Cycle Subsumption Step" notices that `x \in (bc)*` 
;; and `(bc)*` is a left stabilizer of `R = (bc)*`.
;;
;; 1. Subsumption rule triggers: `x` cleanly drops off the front of `x y z "c" x y`.
;; 2. Subsumption rule triggers again: `y` drops off the front of `y z "c" x y`.
;; 3. Subsumption rule triggers again: `z` drops off the front of `z "c" x y`.
;; 4. We are left evaluating `"c" x y \in (bc)*`.
;; 5. Derivative takes "c", evaluates to \emptyset (fail) instantaneously because R expects "b".
;; This file tests that the Subsumption logic can wipe out multiple chained variables flawlessly 
;; without running a single structural Nielsen split.
(check-sat)