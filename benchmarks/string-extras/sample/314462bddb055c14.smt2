; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_6_cross_boundary.smt2
(set-logic ALL)
(declare-fun x () String)

;; R = (abc)*
(define-fun abc () (RegEx String) (str.to_re "abc"))
(define-fun R () (RegEx String) (re.* abc))

;; Constraint: x "bc" x "a" x \in R
;; The "Cross-Boundary Stabilizer Lock"
;; 1. Unwinding x from the left rapidly hits the (abc)* cycle, generating a projection stabilizer for x.
;; 2. Length abstraction fails to detect a conflict: 3|x| + 3 is always divisible by 3, so arithmetically it looks completely SAT.
;; 3. The true conflict: to match `(abc)*` across the first boundary `x bc`, x must definitively start with "a". Let x = "a" + y.
;; 4. When substituting `x = a + y` into `x "a" x`, we logically produce `... a y a a y`.
;; 5. The sequence `a a` is strictly forbidden in the DFA of `(abc)*`.
;; Why this pushes the implementation to its limits: The solver must successfully project the cycle into x', safely bind the trailing segment to x'', and rigorously carry this symbolic decomposition past the literal "bc" onto the second and third instances of x deep into the term to finally unearth the unsatisfiable `a a` overlap.
(assert (str.in_re (str.++ x "bc" x "a" x) R))
(check-sat)