; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_10_linear_form.smt2
(set-logic ALL)
(declare-fun x () String)

;; R = ([a-z]* [0-9])*
;; Tests Section 5.1: Linear Forms and Symbolic Alphabets with character classes.
(define-fun az () (RegEx String) (re.range "a" "z"))
(define-fun az-star () (RegEx String) (re.* az))
(define-fun d09 () (RegEx String) (re.range "0" "9"))
(define-fun R () (RegEx String) (re.* (re.++ az-star d09)))

;; Constraint: x "A" x \in R
;; The letter "A" is neither in [a-z] nor [0-9].
;; This forces the engine to push the unwinding of `x` forwards structurally until it hits the character "A".
;; If `x` unwinds infinitely, it diverges. But because `[a-z]*` and `[0-9]` are symbolic classes,
;; the solver must compute SCCs over the ITE-term evaluations of the symbolic derivatives.
;; It should identify the cyclic repetition of `az-star d09`, extract the stabilizer, decompose `x`,
;; and ultimately crash headfirst into the incompatible "A" character, correctly deducing UNSAT.
(assert (str.in_re (str.++ x "A" x) R))
(check-sat)